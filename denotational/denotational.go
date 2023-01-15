package main

import (
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
	Name  string
	Bound Expression
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
	Body func(v *VarExpr) Expression
}

func Let(name string, init Expression, body func(v *VarExpr) Expression) *LetExpr {
	return &LetExpr{
		Name: name,
		Init: init,
		Body: body,
	}
}

type CloneExpr struct {
	X Expression
}

func Dup(x Expression) (x0, x1 Expression) {
	return &CloneExpr{X: x}, &CloneExpr{X: x}
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
	Body  func(*VarExpr) Expression
}

func Lam(param string, body func(*VarExpr) Expression) *LamExpr {
	return &LamExpr{
		Param: param,
		Body:  body,
	}
}

type Expression interface {
	_expr()
}

func (_ *LitExpr) _expr()   {}
func (_ *AppExpr) _expr()   {}
func (_ *VarExpr) _expr()   {}
func (_ *ConsExpr) _expr()  {}
func (_ *LetExpr) _expr()   {}
func (_ *CloneExpr) _expr() {}
func (_ *Op2Expr) _expr()   {}
func (_ *LamExpr) _expr()   {}

// Returns nil if the rule does not match.
type Rule func(*Machine, Expression) Expression

type Machine struct {
	rules []Rule
}

func (vm *Machine) Rewrite(x *Expression) {
rewrite:
	for {
		for _, rule := range vm.rules {
			y := rule(vm, *x)
			if y != nil {
				*x = y
				continue rewrite
			}
		}
		return
	}
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
	printer.Print(x)
	fmt.Println()
}

func (printer *Printer) Fresh(name string) *VarExpr {
	v := &VarExpr{
		Name: name,
	}
	id := printer.counter
	printer.counter++
	printer.varIDs[v] = id
	return v
}

func (printer *Printer) printf(format string, v ...interface{}) {
	_, _ = fmt.Fprintf(printer.w, format, v...)
}

func (printer *Printer) Print(x Expression) {
	switch x := x.(type) {
	case *VarExpr:
		if id, ok := printer.varIDs[x]; ok {
			fmt.Fprintf(printer.w, "%s#%d", x.Name, id)
		} else {
			fmt.Fprintf(printer.w, "%s@%#p", x.Name, x)
		}

	case *ConsExpr:
		printer.printf("(")
		printer.printf("%s", x.Head)
		for _, arg := range x.Body {
			printer.printf(" ")
			printer.Print(arg)
		}
		printer.printf(")")

	case *LetExpr:
		printer.printf("(let ")
		v := printer.Fresh(x.Name)
		printer.Print(v)
		printer.printf(" ")
		printer.Print(x.Init)
		printer.printf(" ")
		printer.Print(x.Body(v))
		printer.printf(")")

	case *LitExpr:
		printer.printf("%v", x.Value)

	case *LamExpr:
		printer.printf("(lam %s", x.Param)
		arg := printer.Fresh(x.Param)
		printer.Print(x.Body(arg))
		printer.printf(")")

	case *Op2Expr:
		printer.printf("(op2 %v ", x.Op.Name)
		printer.Print(x.A)
		printer.printf(" ")
		printer.Print(x.B)
		printer.printf(")")

	default:
		panic(fmt.Errorf("cannot print %T", x))
	}
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
		return Lit(op2.Op.Func(a, b))
	})

	// Bound variable
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		v, ok := x.(*VarExpr)
		if !(ok && v.Bound != nil) {
			return nil
		}
		return v.Bound
	})

	// (Let x init body) => ...
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		let, ok := x.(*LetExpr)
		if !ok {
			return nil
		}
		v := vm.Fresh(let.Name)
		v.Bound = let.Init
		return let.Body(v)
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
		lst, ok := x.(*ConsExpr)
		if !(ok && lst.Head == "Cons" && len(m.Body) == 2) {
			return nil
		}
		f0, f1 := Dup(m.Body[0])
		first := lst.Body[0]
		rest := lst.Body[1]
		return Cons("Cons", first, App(f0, Cons("Map", f1, rest)))
	})

	sep := ""
	runMain := func(x Expression) {
		fmt.Print(sep)
		sep = "\n\n"
		fmt.Print("Input:\n\n")
		DumpExpression(x)
		fmt.Print("\n")
		vm.Rewrite(&x)
		fmt.Printf("Output:\n\n")
		DumpExpression(x)
	}

	{
		x := vm.Fresh("x")
		y := vm.Fresh("y")
		runMain(Cons("Fst", Cons("Pair", x, y)))
	}

	{
		/*
			let list = (Cons 1 (Cons 2 Nil))
			let add1 = λx (+ x 1)
			(Map add1 list)
		*/
		runMain(
			Let("list", Cons("Cons", Lit(1), Cons("Cons", Lit(2), Cons("Nil"))),
				func(list *VarExpr) Expression {
					return Let("add1", Lam("x", func(x *VarExpr) Expression {
						return Op2(Add, x, Lit(1))
					}), func(add1 *VarExpr) Expression {
						return Cons("Map", add1, list)
					})
				}),
		)
	}
}
