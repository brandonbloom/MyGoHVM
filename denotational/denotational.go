package main

import (
	"errors"
	"fmt"
	"io"
	"os"
)

type Value any

type LitExpr struct {
	Value Value
}

func Lit(x Value) *LitExpr {
	return &LitExpr{Value: x}
}

type VarExpr struct {
	Name string
}

type ConsExpr struct {
	Ctor string
	Args []Expression
}

func Cons(ctor string, args ...Expression) *ConsExpr {
	return &ConsExpr{
		Ctor: ctor,
		Args: args,
	}
}

type AppExpr struct {
	Func Expression
	Arg  Expression
}

func App(f Expression, x Expression) *AppExpr {
	return &AppExpr{
		Func: f,
		Arg:  x,
	}
}

type LetExpr struct {
	Names []string
	Inits []Expression
	Cont  Continuation
}

func LetParallel(names []string, inits []Expression, body func(v ...*VarExpr) Expression) *LetExpr {
	return &LetExpr{
		Names: names,
		Inits: inits,
		Cont:  makeCont(names, body),
	}
}

type Binding struct {
	Name string
	Init Expression
}

func Let(bindings []Binding, body func(v ...*VarExpr) Expression) *LetExpr {
	n := len(bindings)
	names := make([]string, n)
	inits := make([]Expression, n)
	for i, binding := range bindings {
		names[i] = binding.Name
		inits[i] = binding.Init
	}
	return LetParallel(names, inits, body)
}

func Let1(name string, init Expression, body func(v *VarExpr) Expression) *LetExpr {
	return LetParallel([]string{name}, []Expression{init}, func(vars ...*VarExpr) Expression {
		return body(vars[0])
	})
}

// TODO: Variadic.
type DupExpr struct {
	Label int64
	NameA string
	NameB string
	Init  Expression
	Cont  Continuation
}

func Dup(label int64, nameA, nameB string, init Expression, f func(*VarExpr, *VarExpr) Expression) *DupExpr {
	return &DupExpr{
		Label: label,
		NameA: nameA,
		NameB: nameB,
		Init:  init,
		Cont:  makeDupCont(nameA, nameB, f),
	}
}

type SupExpr struct {
	Label int64
	A     Expression
	B     Expression
}

func Sup(label int64, a, b Expression) *SupExpr {
	return &SupExpr{label, a, b}
}

type Op2Expr struct {
	Op Operator
	A  Expression
	B  Expression
}

type Operator struct {
	Name string
	Func func(Value, Value) Value
}

func Op2(op Operator, a, b Expression) *Op2Expr {
	return &Op2Expr{
		Op: op,
		A:  a,
		B:  b,
	}
}

// TODO: Variadic.
type LamExpr struct {
	Param string
	Cont  Continuation
}

func Lam(param string, body func(arg *VarExpr) Expression) *LamExpr {
	return &LamExpr{
		Param: param,
		Cont:  makeLamCont(param, body),
	}
}

type Expression interface {
	Visit(Visitor)
}

type Visitor interface {
	VisitLit(*LitExpr)
	VisitApp(*AppExpr)
	VisitVar(*VarExpr)
	VisitCons(*ConsExpr)
	VisitLet(*LetExpr)
	VisitDup(*DupExpr)
	VisitSup(*SupExpr)
	VisitOp2(*Op2Expr)
	VisitLam(*LamExpr)
}

func (x *LitExpr) Visit(v Visitor)  { v.VisitLit(x) }
func (x *AppExpr) Visit(v Visitor)  { v.VisitApp(x) }
func (x *VarExpr) Visit(v Visitor)  { v.VisitVar(x) }
func (x *ConsExpr) Visit(v Visitor) { v.VisitCons(x) }
func (x *LetExpr) Visit(v Visitor)  { v.VisitLet(x) }
func (x *DupExpr) Visit(v Visitor)  { v.VisitDup(x) }
func (x *SupExpr) Visit(v Visitor)  { v.VisitSup(x) }
func (x *Op2Expr) Visit(v Visitor)  { v.VisitOp2(x) }
func (x *LamExpr) Visit(v Visitor)  { v.VisitLam(x) }

type Continuation struct {
	X     *Expression
	Holes []*Expression
}

func (k Continuation) FillHoles(xs ...Expression) Expression {
	for i, x := range xs {
		*k.Holes[i] = x
	}
	return *k.X
}

func makeCont(holes []string, f func(...*VarExpr) Expression) Continuation {
	vars := make([]*VarExpr, len(holes))
	for i, hole := range holes {
		vars[i] = &VarExpr{hole}
	}
	x := f(vars...)
	cb := newContBuilder(vars...)
	cb.visitChild(&x)
	for i, hole := range cb.holes {
		if hole == nil {
			panic(fmt.Errorf("hole not found: %s", holes[i]))
		}
	}
	return Continuation{
		X:     &x,
		Holes: cb.holes,
	}
}

func makeLamCont(hole string, f func(*VarExpr) Expression) Continuation {
	return makeCont([]string{hole}, func(vars ...*VarExpr) Expression {
		return f(vars[0])
	})
}

func makeDupCont(holeA, holeB string, f func(*VarExpr, *VarExpr) Expression) Continuation {
	return makeCont([]string{holeA, holeB}, func(vars ...*VarExpr) Expression {
		return f(vars[0], vars[1])
	})
}

type contBuilder struct {
	variables []*VarExpr    // Variables to find the addresses of.
	holes     []*Expression // Found addresses of parallel found variables.
	visited   Expression    // Current expression in post-order traversal.
}

func newContBuilder(variables ...*VarExpr) *contBuilder {
	return &contBuilder{
		variables: variables,
		holes:     make([]*Expression, len(variables)),
	}
}

func (cb *contBuilder) visitChild(x *Expression) {
	(*x).Visit(cb)
	cb.visited = *x
	if v, ok := cb.visited.(*VarExpr); ok {
		for i, candidate := range cb.variables {
			if candidate == v {
				cb.holes[i] = x
			}
		}
	}
}

func (cb *contBuilder) VisitLit(lit *LitExpr) {
	// No children.
}

func (cb *contBuilder) VisitApp(app *AppExpr) {
	cb.visitChild(&app.Func)
	cb.visitChild(&app.Arg)
}

func (cb *contBuilder) VisitVar(v *VarExpr) {
	// No children.
}

func (cb *contBuilder) VisitCons(cons *ConsExpr) {
	for i := range cons.Args {
		cb.visitChild(&cons.Args[i])
	}
}

func (cb *contBuilder) VisitLet(let *LetExpr) {
	for i := range let.Inits {
		cb.visitChild(&let.Inits[i])
	}
	cb.visitChild(let.Cont.X)
}

func (cb *contBuilder) VisitDup(dup *DupExpr) {
	cb.visitChild(&dup.Init)
	cb.visitChild(dup.Cont.X)
}

func (cb *contBuilder) VisitSup(sup *SupExpr) {
	cb.visitChild(&sup.A)
	cb.visitChild(&sup.B)
}

func (cb *contBuilder) VisitOp2(op2 *Op2Expr) {
	cb.visitChild(&op2.A)
	cb.visitChild(&op2.B)
}

func (cb *contBuilder) VisitLam(lam *LamExpr) {
	cb.visitChild(lam.Cont.X)
}

// Returns nil if the rule does not match.
type Rule func(*Machine, Expression) Expression

type Machine struct {
	dupCount int64
	rules    []Rule
}

func (vm *Machine) FreshDupLabel() int64 {
	vm.dupCount++
	return vm.dupCount
}

func (vm *Machine) Normalize(x *Expression) (changed bool) {
	loop := true
	for loop {
		loop = vm.Rewrite(x)

		switch x := (*x).(type) {
		case *ConsExpr:
			for i := range x.Args {
				loop = loop || vm.Normalize(&x.Args[i])
			}

		case *LetExpr:
			for i := range x.Inits {
				loop = loop || vm.Normalize(&x.Inits[i])
			}
			loop = loop || vm.Normalize(x.Cont.X)

		case *DupExpr:
			loop = loop || vm.Normalize(&x.Init)
			loop = loop || vm.Normalize(x.Cont.X)

		case *AppExpr:
			loop = loop || vm.Normalize(&x.Func)
			loop = loop || vm.Normalize(&x.Arg)

		case *LamExpr:
			loop = loop || vm.Normalize(x.Cont.X)

		case *Op2Expr:
			loop = loop || vm.Normalize(&x.A)
			loop = loop || vm.Normalize(&x.B)

		case *VarExpr, *LitExpr, *SupExpr:
			// No-op.

		default:
			panic(fmt.Errorf("cannot normalize %T", x))
		}

		changed = changed || loop
	}
	return
}

func (vm *Machine) Rewrite(x *Expression) (changed bool) {
	limit := -1
rewrite:
	for fuel := limit; fuel != 0; fuel-- {
		for _, rule := range vm.rules {
			y := rule(vm, *x)
			if y != nil {
				*x = y
				changed = true
				continue rewrite
			}
		}
		return
	}
	panic(errors.New("out of fuel"))
}

func (vm *Machine) FreshVar(name string) *VarExpr {
	return &VarExpr{
		Name: name,
	}
}

func (vm *Machine) AddRule(rule Rule) {
	vm.rules = append(vm.rules, rule)
}

type Printer struct {
	w       io.Writer
	varIDs  map[*VarExpr]int64
	counter int64
}

func NewPrinter(w io.Writer) *Printer {
	return &Printer{
		w:      w,
		varIDs: make(map[*VarExpr]int64),
	}
}

func DumpExpression(x Expression) {
	printer := NewPrinter(os.Stdout)
	x.Visit(printer)
	fmt.Println()
}

func (printer *Printer) freshVar(name string, x *Expression) *VarExpr {
	v := (*x).(*VarExpr)
	id := printer.counter
	printer.counter++
	printer.varIDs[v] = id
	return v
}

func (printer *Printer) printf(format string, v ...interface{}) {
	_, _ = fmt.Fprintf(printer.w, format, v...)
}

func (printer *Printer) VisitVar(v *VarExpr) {
	if id, ok := printer.varIDs[v]; ok {
		fmt.Fprintf(printer.w, "%s#%d", v.Name, id)
	} else {
		fmt.Fprintf(printer.w, "%s@%#p", v.Name, v)
	}
}

func (printer *Printer) VisitCons(cons *ConsExpr) {
	if len(cons.Args) == 0 {
		printer.printf("%s", cons.Ctor)
	} else {
		printer.printf("(")
		printer.printf("%s", cons.Ctor)
		for _, arg := range cons.Args {
			printer.printf(" ")
			arg.Visit(printer)
		}
		printer.printf(")")
	}
}

func (printer *Printer) VisitApp(app *AppExpr) {
	printer.printf("(")
	app.Func.Visit(printer)
	printer.printf(" ")
	app.Arg.Visit(printer)
	printer.printf(")")
}

func (printer *Printer) VisitDup(dup *DupExpr) {
	printer.printf("(dup %d ", dup.Label)
	a := printer.freshVar(dup.NameA, dup.Cont.Holes[0])
	a.Visit(printer)
	printer.printf(" ")
	b := printer.freshVar(dup.NameB, dup.Cont.Holes[1])
	b.Visit(printer)
	printer.printf(" ")
	dup.Init.Visit(printer)
	printer.printf(" ")
	(*dup.Cont.X).Visit(printer)
	printer.printf(")")
}

func (printer *Printer) VisitSup(sup *SupExpr) {
	printer.printf("#sup[%d ", sup.Label)
	sup.A.Visit(printer)
	printer.printf(" ")
	sup.B.Visit(printer)
	printer.printf("]")
}

func (printer *Printer) VisitLet(let *LetExpr) {
	printer.printf("(let {")
	sep := ""
	for i := range let.Names {
		printer.printf(sep)
		v := printer.freshVar(let.Names[i], let.Cont.Holes[i])
		v.Visit(printer)
		printer.printf(" ")
		let.Inits[i].Visit(printer)
		sep = ", "
	}
	printer.printf("} ")
	(*let.Cont.X).Visit(printer)
	printer.printf(")")
}

func (printer *Printer) VisitLit(lit *LitExpr) {
	switch v := lit.Value.(type) {
	case int:
		printer.printf("%d", v)
	case string:
		printer.printf("%q", v)
	default:
		printer.printf("<%v>", v)
	}
}

func (printer *Printer) VisitLam(lam *LamExpr) {
	printer.printf("(lam ")
	v := printer.freshVar(lam.Param, lam.Cont.Holes[0])
	v.Visit(printer)
	printer.printf(" ")
	(*lam.Cont.X).Visit(printer)
	printer.printf(")")
}

func (printer *Printer) VisitOp2(op2 *Op2Expr) {
	printer.printf("(op2 %v ", op2.Op.Name)
	op2.A.Visit(printer)
	printer.printf(" ")
	op2.B.Visit(printer)
	printer.printf(")")
}

var Add = Operator{
	Name: "Add",
	Func: func(a, b Value) Value {
		return a.(int) + b.(int)
	},
}

func addressOf[T any](x T) *T {
	return &x
}

func main() {
	vm := &Machine{}

	// TODO: Avoid runtime pattern matching on builtins.
	// Do this by encoding builtin rules as expressions with eval method.
	// Move the matching into the factory functions.

	// (Op2 f a b) = ...
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		op2, ok := x.(*Op2Expr)
		if !ok {
			return nil
		}
		a, ok := op2.A.(*LitExpr)
		if !ok {
			return nil
		}
		b, ok := op2.A.(*LitExpr)
		if !ok {
			return nil
		}
		return Lit(op2.Op.Func(a.Value, b.Value))
	})

	// (Let {x init, ...} body) => ...
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		let, ok := x.(*LetExpr)
		if !ok {
			return nil
		}
		return let.Cont.FillHoles(let.Inits...)
	})

	// (Dup a b (Lit ...) k)
	// ---------------------
	// (k a b ...)
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		dup, ok := x.(*DupExpr)
		if !ok {
			return nil
		}
		lit, ok := dup.Init.(*LitExpr)
		if !ok {
			return nil
		}
		return dup.Cont.FillHoles(lit, lit)
	})

	// (Dup a b (Cons ctor args...) k)
	// ----------------------------- Dup-Cons
	// dup a0 a1 = a
	// dup b0 b1 = b
	// ...
	// (k (Foo a0 b0 ...) (Foo a1 b1 ...))
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		dup, ok := x.(*DupExpr)
		if !ok {
			return nil
		}
		cons, ok := dup.Init.(*ConsExpr)
		if !ok {
			return nil
		}
		arity := len(cons.Args)
		argsA := make([]Expression, arity)
		argsB := make([]Expression, arity)
		for i, child := range cons.Args {
			Dup(dup.Label, "a", "b", child, func(a, b *VarExpr) Expression {
				argsA[i] = a
				argsB[i] = b
				return nil // XXX
			})
		}
		consA := Cons(cons.Ctor, argsA...)
		consB := Cons(cons.Ctor, argsB...)
		return dup.Cont.FillHoles(consA, consB)
	})

	/*
		(Dup a b (Lam param body) k)

		dup a b = λx(body)
		------------------ Dup-Lam
		a <- λx0(b0)
		b <- λx1(b1)
		x <- {x0 x1}
		dup b0 b1 = body
	*/
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		dup, ok := x.(*DupExpr)
		if !ok {
			return nil
		}
		lam, ok := dup.Init.(*LamExpr)
		if !ok {
			return nil
		}

		var x0 Expression = &VarExpr{"x0"}
		var x1 Expression = &VarExpr{"x1"}
		sup := Sup(dup.Label, x0, x1)
		body := lam.Cont.FillHoles(sup)
		var b0 Expression = &VarExpr{"b0"}
		var b1 Expression = &VarExpr{"b1"}
		return &DupExpr{
			NameA: "b0",
			NameB: "b1",
			Init:  body,
			Cont: Continuation{
				X: addressOf[Expression](&LetExpr{
					Names: []string{"a", "b"},
					Inits: []Expression{
						&LamExpr{
							Param: "x0",
							Cont: Continuation{
								X:     &b0,
								Holes: []*Expression{&sup.A},
							},
						},
						&LamExpr{
							Param: "x1",
							Cont: Continuation{
								X:     &b1,
								Holes: []*Expression{&sup.B},
							},
						},
					},
					Cont: dup.Cont,
				}),
				Holes: []*Expression{&b0, &b1},
			},
		}
	})

	/*
	  (+ {a0 a1} b)
	  --------------------- Op2-Sup-A
	  dup b0 b1 = b
	  {(+ a0 b0) (+ a1 b1)}
	*/
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		op2, ok := x.(*Op2Expr)
		if !ok {
			return nil
		}
		sup, ok := op2.A.(*SupExpr)
		if !ok {
			return nil
		}
		b := op2.B
		op := op2.Op
		a0 := sup.A
		a1 := sup.B
		return Dup(sup.Label, "b0", "b1", b, func(b0, b1 *VarExpr) Expression {
			return Sup(sup.Label, Op2(op, a0, b0), Op2(op, a1, b1))
		})
	})

	/*
		(+ a {b0 b1})
		--------------------- Op2-Sup-B
		dup a0 a1 = a
		{(+ a0 b0) (+ a1 b1)}
	*/
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		op2, ok := x.(*Op2Expr)
		if !ok {
			return nil
		}
		sup, ok := op2.B.(*SupExpr)
		if !ok {
			return nil
		}
		a := op2.A
		op := op2.Op
		b0 := sup.A
		b1 := sup.B
		return Dup(sup.Label, "a0", "a1", a, func(a0, a1 *VarExpr) Expression {
			return Sup(sup.Label, Op2(op, a0, b0), Op2(op, a1, b1))
		})
	})

	/*
		(λx(body) arg)
		-------------- App-Lam
		x <- arg
		body
	*/
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		app, ok := x.(*AppExpr)
		if !ok {
			return nil
		}
		lam, ok := app.Func.(*LamExpr)
		if !ok {
			return nil
		}
		return lam.Cont.FillHoles(app.Arg)
	})

	// Dup-Sup.
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		dup, ok := x.(*DupExpr)
		if !ok {
			return nil
		}
		sup, ok := dup.Init.(*SupExpr)
		if !ok {
			return nil
		}
		if dup.Label == sup.Label {
			/*
				When ending the duplication process.

				dup a b = {r s}
				-------- Dup-Sup (base)
				a <- r
				b <- s
			*/
			return dup.Cont.FillHoles(sup.A, sup.B)
		} else {
			/*
				  When duplicating a term, which itself duplicates something.

					dup x y = {a b}
					--------- Dup-Sup (recur)
					x <- {xA xB}
					y <- {yA yB}
					dup xA yA = a
					dup xB yB = b
			*/
			return Dup(dup.Label, "xA", "yA", sup.A, func(xA, yA *VarExpr) Expression {
				return Dup(dup.Label, "xB", "yB", sup.B, func(xB, yB *VarExpr) Expression {
					x := Sup(dup.Label, xA, xB)
					y := Sup(dup.Label, yA, yB)
					return dup.Cont.FillHoles(x, y)
				})
			})
		}
	})

	/////////////

	// (Fst (Pair x y)) = x
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		f, ok := x.(*ConsExpr)
		if !(ok && f.Ctor == "Fst" && len(f.Args) == 1) {
			return nil
		}
		pair, ok := f.Args[0].(*ConsExpr)
		if !(ok && len(pair.Args) == 2) {
			return nil
		}
		return pair.Args[0]
	})

	// (Map f Nil) = Nil
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		m, ok := x.(*ConsExpr)
		if !(ok && m.Ctor == "Map" && len(m.Args) == 2) {
			return nil
		}
		n, ok := x.(*ConsExpr)
		if !(ok && n.Ctor == "Nil" && len(m.Args) == 0) {
			return nil
		}
		return n
	})
	// (Map f (Cons x xs)) = (Cons (f x) (Map f xs))
	mapDupLabel := vm.FreshDupLabel()
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		m, ok := x.(*ConsExpr)
		if !(ok && m.Ctor == "Map" && len(m.Args) == 2) {
			return nil
		}
		f := m.Args[0]
		lst, ok := m.Args[1].(*ConsExpr)
		if !(ok && lst.Ctor == "Cons" && len(m.Args) == 2) {
			return nil
		}
		return Dup(mapDupLabel, "f0", "f1", f, func(f0, f1 *VarExpr) Expression {
			first := lst.Args[0]
			rest := lst.Args[1]
			return Cons("Cons", App(f0, first), Cons("Map", f1, rest))
		})
	})

	sep := ""
	runMain := func(x Expression) {
		fmt.Print(sep)
		sep = "\n\n"
		fmt.Print("Input:\n\n")
		DumpExpression(x)
		fmt.Print("\n")
		_ = vm.Normalize(&x)
		fmt.Printf("Output:\n\n")
		DumpExpression(x)
	}

	{
		x := vm.FreshVar("x")
		y := vm.FreshVar("y")
		runMain(Cons("Fst", Cons("Pair", x, y)))
	}

	{
		runMain(Let1("x", Lit(1), func(x *VarExpr) Expression {
			return x
		}))
	}

	{
		dupLabel := vm.FreshDupLabel()
		runMain(Dup(dupLabel, "x", "y", Lit(1), func(x, y *VarExpr) Expression {
			return Op2(Add, x, y)
		}))
	}

	{
		runMain(App(
			Lam("x", func(x *VarExpr) Expression { return x }),
			Lit(1),
		))
	}

	{
		/*
			let list = (Cons 1 (Cons 2 Nil))
			let inc = λx (+ x 1)
			(Map inc list)
		*/
		runMain(
			Let([]Binding{
				{"list", Cons("Cons", Lit(1), Cons("Cons", Lit(2), Cons("Nil")))},
				{"inc", Lam("x", func(x *VarExpr) Expression {
					return Op2(Add, x, Lit(1))
				})},
			},
				func(vars ...*VarExpr) Expression {
					list := vars[0]
					inc := vars[1]
					return Cons("Map", inc, list)
				}),
		)
	}
}
