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
	Head string
	Body []Expression
}

func Cons(head string, body ...Expression) *ConsExpr {
	return &ConsExpr{
		Head: head,
		Body: body,
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
	Name string
	Init Expression
	Body LetCont
}

func Let(name string, init Expression, body func(v *VarExpr) Expression) *LetExpr {
	return &LetExpr{
		Name: name,
		Init: init,
		Body: makeLetCont(name, body),
	}
}

type DupExpr struct {
	NameA string
	NameB string
	Init  Expression
	Body  DupCont
}

func Dup(nameA, nameB string, init Expression, f func(*VarExpr, *VarExpr) Expression) *DupExpr {
	return &DupExpr{
		NameA: nameA,
		NameB: nameB,
		Init:  init,
		Body:  makeDupCont(nameA, nameB, f),
	}
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

type LamExpr struct {
	Param string
	Body  LamCont
}

func Lam(param string, body func(arg *VarExpr) Expression) *LamExpr {
	return &LamExpr{
		Param: param,
		Body:  makeLamCont(param, body),
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
	VisitOp2(*Op2Expr)
	VisitLam(*LamExpr)
}

func (x *LitExpr) Visit(v Visitor)  { v.VisitLit(x) }
func (x *AppExpr) Visit(v Visitor)  { v.VisitApp(x) }
func (x *VarExpr) Visit(v Visitor)  { v.VisitVar(x) }
func (x *ConsExpr) Visit(v Visitor) { v.VisitCons(x) }
func (x *LetExpr) Visit(v Visitor)  { v.VisitLet(x) }
func (x *DupExpr) Visit(v Visitor)  { v.VisitDup(x) }
func (x *Op2Expr) Visit(v Visitor)  { v.VisitOp2(x) }
func (x *LamExpr) Visit(v Visitor)  { v.VisitLam(x) }

type LetCont struct {
	X    *Expression
	Hole *Expression
}

type LamCont = LetCont // Both are arity 1.

type DupCont struct {
	X     *Expression
	HoleA *Expression
	HoleB *Expression
}

func (k LetCont) FillHole(x Expression) Expression {
	*k.Hole = x
	return *k.X
}

func (k DupCont) FillHoles(a Expression, b Expression) Expression {
	*k.HoleA = a
	*k.HoleB = b
	return *k.X
}

func makeLetCont(hole string, f func(*VarExpr) Expression) LetCont {
	v := &VarExpr{hole}
	x := f(v)
	c := &contBuilder{
		holes: []holeBuilder{
			{variable: v},
		},
	}
	c.visitChild(&x)
	_ = (*c.holes[0].location).(*VarExpr)
	return LetCont{
		X:    &x,
		Hole: c.holes[0].location,
	}
}

var makeLamCont = makeLetCont

func makeDupCont(holeA, holeB string, f func(*VarExpr, *VarExpr) Expression) DupCont {
	a := &VarExpr{holeA}
	b := &VarExpr{holeB}
	x := f(a, b)
	c := &contBuilder{
		holes: []holeBuilder{
			{variable: a},
			{variable: b},
		},
	}
	c.visitChild(&x)
	_ = (*c.holes[0].location).(*VarExpr)
	_ = (*c.holes[1].location).(*VarExpr)
	return DupCont{
		X:     &x,
		HoleA: c.holes[0].location,
		HoleB: c.holes[0].location,
	}
}

type contBuilder struct {
	holes   []holeBuilder
	visited Expression // Current expression in post-order traversal.
}

type holeBuilder struct {
	variable *VarExpr    // Variable to find the address of.
	location *Expression // Points to variable found in expression.
}

func (cb *contBuilder) visitChild(x *Expression) {
	(*x).Visit(cb)
	cb.visited = *x
	if v, ok := cb.visited.(*VarExpr); ok {
		for i, hole := range cb.holes {
			if v == hole.variable {
				cb.holes[i].location = x
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
	for i := range cons.Body {
		cb.visitChild(&cons.Body[i])
	}
}

func (cb *contBuilder) VisitLet(let *LetExpr) {
	cb.visitChild(&let.Init)
	cb.visitChild(let.Body.X)
}

func (cb *contBuilder) VisitDup(dup *DupExpr) {
	cb.visitChild(&dup.Init)
	cb.visitChild(dup.Body.X)
}

func (cb *contBuilder) VisitOp2(op2 *Op2Expr) {
	cb.visitChild(&op2.A)
	cb.visitChild(&op2.B)
}

func (cb *contBuilder) VisitLam(lam *LamExpr) {
	cb.visitChild(lam.Body.X)
}

// Returns nil if the rule does not match.
type Rule func(*Machine, Expression) Expression

type Machine struct {
	rules []Rule
}

func (vm *Machine) Normalize(x *Expression) {
	vm.Rewrite(x)
	// TODO: Normalize within lets and lambdas too?
	if cons, ok := (*x).(*ConsExpr); ok {
		for i := range cons.Body {
			vm.Normalize(&cons.Body[i])
		}
	}
}

func (vm *Machine) Rewrite(x *Expression) {
	limit := -1
rewrite:
	for fuel := limit; fuel != 0; fuel-- {
		for _, rule := range vm.rules {
			y := rule(vm, *x)
			if y != nil {
				*x = y
				continue rewrite
			}
		}
		return
	}
	panic(errors.New("out of fuel"))
}

func (vm *Machine) Fresh(name string) *VarExpr {
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

func (printer *Printer) fresh(name string, x *Expression) *VarExpr {
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
	if len(cons.Body) == 0 {
		printer.printf("%s", cons.Head)
	} else {
		printer.printf("(")
		printer.printf("%s", cons.Head)
		for _, arg := range cons.Body {
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
	printer.printf("(dup ")
	a := printer.fresh(dup.NameA, dup.Body.HoleA)
	a.Visit(printer)
	printer.printf(" ")
	b := printer.fresh(dup.NameB, dup.Body.HoleB)
	b.Visit(printer)
	printer.printf(" ")
	dup.Init.Visit(printer)
	printer.printf(" ")
	(*dup.Body.X).Visit(printer)
	printer.printf(")")
}

func (printer *Printer) VisitLet(let *LetExpr) {
	printer.printf("(let ")
	v := printer.fresh(let.Name, let.Body.Hole)
	v.Visit(printer)
	printer.printf(" ")
	let.Init.Visit(printer)
	printer.printf(" ")
	(*let.Body.X).Visit(printer)
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
	v := printer.fresh(lam.Param, lam.Body.Hole)
	v.Visit(printer)
	printer.printf(" ")
	(*lam.Body.X).Visit(printer)
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

func main() {
	vm := &Machine{}

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

	// (Let x init body) => ...
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		let, ok := x.(*LetExpr)
		if !ok {
			return nil
		}
		return let.Body.FillHole(let.Init)
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
		return dup.Body.FillHoles(lit, lit)
	})

	// (Dup a b (Cons head body...) k)
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
		arity := len(cons.Body)
		bodyA := make([]Expression, arity)
		bodyB := make([]Expression, arity)
		for i, child := range cons.Body {
			Dup("a", "b", child, func(a, b *VarExpr) Expression {
				bodyA[i] = a
				bodyB[i] = b
				return nil // XXX
			})
		}
		consA := Cons(cons.Head, bodyA...)
		consB := Cons(cons.Head, bodyB...)
		return dup.Body.FillHoles(consA, consB)
	})

	// (Dup a b (Lam param body) k)
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		dup, ok := x.(*DupExpr)
		if !ok {
			return nil
		}
		lam, ok := dup.Init.(*LamExpr)
		if !ok {
			return nil
		}
		_ = lam    // XXX
		return nil // XXX
	})

	// (Fst (Pair x y)) = x
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		f, ok := x.(*ConsExpr)
		if !(ok && f.Head == "Fst" && len(f.Body) == 1) {
			return nil
		}
		pair, ok := f.Body[0].(*ConsExpr)
		if !(ok && len(pair.Body) == 2) {
			return nil
		}
		return pair.Body[0]
	})

	// (Map f Nil) = Nil
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		m, ok := x.(*ConsExpr)
		if !(ok && m.Head == "Map" && len(m.Body) == 2) {
			return nil
		}
		n, ok := x.(*ConsExpr)
		if !(ok && n.Head == "Nil" && len(m.Body) == 0) {
			return nil
		}
		return n
	})
	// (Map f (Cons x xs)) = (Cons (f x) (Map f xs))
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		m, ok := x.(*ConsExpr)
		if !(ok && m.Head == "Map" && len(m.Body) == 2) {
			return nil
		}
		f := m.Body[0]
		lst, ok := m.Body[1].(*ConsExpr)
		if !(ok && lst.Head == "Cons" && len(m.Body) == 2) {
			return nil
		}
		return Dup("f0", "f1", f, func(f0, f1 *VarExpr) Expression {
			first := lst.Body[0]
			rest := lst.Body[1]
			return Cons("Cons", first, App(f0, Cons("Map", f1, rest)))
		})
	})

	sep := ""
	runMain := func(x Expression) {
		fmt.Print(sep)
		sep = "\n\n"
		fmt.Print("Input:\n\n")
		DumpExpression(x)
		fmt.Print("\n")
		vm.Normalize(&x)
		fmt.Printf("Output:\n\n")
		DumpExpression(x)
	}

	{
		x := vm.Fresh("x")
		y := vm.Fresh("y")
		runMain(Cons("Fst", Cons("Pair", x, y)))
	}

	{
		runMain(Let("x", Lit(1), func(x *VarExpr) Expression {
			return x
		}))
	}

	{
		runMain(Dup("x", "y", Lit(1), func(x, y *VarExpr) Expression {
			return Op2(Add, x, y)
		}))
	}

	{
		/*
			let list = (Cons 1 (Cons 2 Nil))
			let inc = λx (+ x 1)
			(Map inc list)
		*/
		runMain(
			Let("list",
				Cons("Cons", Lit(1), Cons("Cons", Lit(2), Cons("Nil"))),
				func(list *VarExpr) Expression {
					return Let("inc",
						Lam("x", func(x *VarExpr) Expression {
							return Op2(Add, x, Lit(1))
						}),
						func(inc *VarExpr) Expression {
							return Cons("Map", inc, list)
						})
				}),
		)
	}
}
