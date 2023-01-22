package main

import (
	"fmt"

	. "github.com/brandonbloom/MyGoHVm/internal"
)

func main() {
	vm := NewMachine()
	//vm.Trace = true

	// (Left (Pair x y)) = x
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		f, ok := x.(*ConsExpr)
		if !(ok && f.Ctor == "Left" && len(f.Args) == 1) {
			return nil
		}
		pair, ok := f.Args[0].(*ConsExpr)
		if !(ok && len(pair.Args) == 2) {
			return nil
		}
		return pair.Args[0]
	})

	// (Right (Pair x y)) = y
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		f, ok := x.(*ConsExpr)
		if !(ok && f.Ctor == "Right" && len(f.Args) == 1) {
			return nil
		}
		pair, ok := f.Args[0].(*ConsExpr)
		if !(ok && len(pair.Args) == 2) {
			return nil
		}
		return pair.Args[1]
	})

	// (Map f Nil) = Nil
	vm.AddRule(func(vm *Machine, x Expression) Expression {
		m, ok := x.(*ConsExpr)
		if !(ok && m.Ctor == "Map" && len(m.Args) == 2) {
			return nil
		}
		lst, ok := m.Args[1].(*ConsExpr)
		if !(ok && lst.Ctor == "Nil" && len(lst.Args) == 0) {
			return nil
		}
		return lst
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
		if !(ok && lst.Ctor == "Cons" && len(lst.Args) == 2) {
			return nil
		}
		return Dup(mapDupLabel, "f0", "f1", f, func(f0, f1 *VarExpr) Expression {
			first := lst.Args[0]
			rest := lst.Args[1]
			return Cons("Cons", App(f0, first), Cons("Map", f1, rest))
		})
	})

	//////////////

	sep := ""
	runMain := func(x Expression) {
		fmt.Print(sep)
		sep = "\n\n"
		fmt.Print("Input:\n\n")
		DumpExpression(x)
		fmt.Print("\n")
		y := vm.Normalize(x)
		fmt.Printf("Output:\n\n")
		DumpExpression(y)
	}

	{
		runMain(Cons("Left", Cons("Pair", Var("x"), Var("y"))))
	}

	{
		runMain(Let1("x", Lit(1), func(x *VarExpr) Expression {
			return x
		}))
	}

	{
		runMain(Op2(Add, Lit(2), Lit(3)))
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
		runMain(Cons("Pair", Lit(1), Lit(2)))
	}

	{
		// Shadowing.
		runMain(Let1("x", Lit(1), func(x *VarExpr) Expression {
			return Erase(x, Let1("x", Lit(2), func(x *VarExpr) Expression {
				return x
			}))
		}))
	}

	{
		dupLabel := vm.FreshDupLabel()
		runMain(Dup(dupLabel, "x0", "x1", Cons("Pair", Lit(1), Lit(2)), func(x0, x1 *VarExpr) Expression {
			return Dup(dupLabel, "x00", "x01", x0, func(x00, x01 *VarExpr) Expression {
				return Dup(dupLabel, "x10", "x11", x1, func(x10, x11 *VarExpr) Expression {
					return Cons("Quad", Cons("Left", x00), Cons("Right", x01), Cons("Left", x10), Cons("Right", x11))
				})
			})
		}))
	}

	{
		runMain(Let1("x", Lit(1), func(x *VarExpr) Expression {
			return Erase(x, Lit(2))
		}))
	}

	{
		// Dup lambdas, but don't apply them.
		dupLabel := vm.FreshDupLabel()
		runMain(Dup(dupLabel, "f1", "f2", Lam("x", func(x *VarExpr) Expression {
			return Op2(Add, x, Lit(1))
		}), func(f1, f2 *VarExpr) Expression {
			return Cons("Pair", f1, f2)
		}))
	}

	{
		// Dup and apply lambdas that ignore the argument.
		dupLabel := vm.FreshDupLabel()
		runMain(Dup(dupLabel, "f1", "f2", Lam("x", func(x *VarExpr) Expression {
			return Erase(x, Lit(1))
		}), func(f1, f2 *VarExpr) Expression {
			return Cons("Pair", App(f1, Lit(2)), App(f2, Lit(3)))
		}))
	}

	{
		dupLabel := vm.FreshDupLabel()
		runMain(Sup(dupLabel, Lit(1), Lit(2)))
	}

	{
		dupLabel := vm.FreshDupLabel()
		runMain(Dup(dupLabel, "a", "b", Sup(dupLabel, Lit(1), Lit(2)), func(a, b *VarExpr) Expression {
			return Cons("Pair", a, b)
		}))
	}

	{
		// Dup and apply typical lambdas.
		dupLabel := vm.FreshDupLabel()
		runMain(Dup(dupLabel, "f1", "f2", Lam("x", func(x *VarExpr) Expression {
			return Op2(Add, x, Lit(1))
		}), func(f1, f2 *VarExpr) Expression {
			return Cons("Pair", App(f1, Lit(2)), App(f2, Lit(3)))
		}))
	}

	{
		runMain(
			Cons("Map", Lam("x", func(x *VarExpr) Expression { return x }), Cons("Nil")),
		)
	}

	{
		/*
			let list = (Cons 1 (Cons 2 Nil))
			let inc = λx (+ x 1)
			(Map inc list)
		*/
		runMain(
			Let([]Binding{
				MakeBinding("list", Cons("Cons", Lit(1), Cons("Cons", Lit(2), Cons("Nil")))),
				MakeBinding("inc", Lam("x", func(x *VarExpr) Expression {
					return Op2(Add, x, Lit(1))
				})),
			},
				func(vars ...*VarExpr) Expression {
					list := vars[0]
					inc := vars[1]
					return Cons("Map", inc, list)
				}),
		)
	}

	// TODO: User-level operators to collapse sups.
}
