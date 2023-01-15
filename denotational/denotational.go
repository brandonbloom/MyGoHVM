package main

import (
	"fmt"
	"io"
	"os"
)

type Value any

type Variable struct {
	Name string
	ID   int64
}

type Symbol struct {
	Name string
}

type Expression interface {
	_expr()
}

type Constructor struct {
	Head Symbol
	Body []Expression
}

func Cons(head Symbol, body ...Expression) *Constructor {
	return &Constructor{
		Head: head,
		Body: body,
	}
}

type Let struct {
	Var  Variable
	Init Expression
	Body Expression
}

func (_ *Variable) _expr()    {}
func (_ *Constructor) _expr() {}

type Rule func(*Machine, Expression) Expression

type Machine struct {
	counter int64
	rules   []Rule
}

func (vm *Machine) Fresh(name string) *Variable {
	id := vm.counter
	vm.counter++
	return &Variable{
		Name: name,
		ID:   id,
	}
}

func (vm *Machine) Reduce(x Expression) Expression {
rewrite:
	for {
		for _, rule := range vm.rules {
			y := rule(vm, x)
			if y != nil {
				x = y
				continue rewrite
			}
		}
		return x
	}
}

func (vm *Machine) AddRule(rule Rule) {
	vm.rules = append(vm.rules, rule)
}

func DumpExpression(x Expression) {
	WriteExpressionTo(os.Stdout, x)
	fmt.Println()
}

func WriteExpressionTo(w io.Writer, x Expression) {
	switch x := x.(type) {
	case *Variable:
		fmt.Fprintf(w, "%s#%d", x.Name, x.ID)
	case *Constructor:
		io.WriteString(w, "(")
		io.WriteString(w, x.Head.Name)
		for _, arg := range x.Body {
			io.WriteString(w, " ")
			WriteExpressionTo(w, arg)
		}
		io.WriteString(w, ")")
	default:
		panic(fmt.Errorf("cannot dump %T", x))
	}
}

func main() {
	vm := &Machine{}
	fst := Symbol{"Fst"}
	pair := Symbol{"Pair"}
	x := vm.Fresh("x")
	y := vm.Fresh("y")

	// (Fst (Pair x y)) = x
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		f, ok := x.(*Constructor)
		if !ok {
			return nil
		}
		if f.Head.Name != "Fst" {
			return nil
		}
		if len(f.Body) != 1 {
			return nil
		}
		pair, ok := f.Body[0].(*Constructor)
		if !ok {
			return nil
		}
		if len(pair.Body) != 2 {
			return nil
		}
		return pair.Body[0]
	})

	result := vm.Reduce(Cons(fst, Cons(pair, x, y)))
	DumpExpression(result)
}
