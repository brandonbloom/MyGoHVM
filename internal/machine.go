package internal

import "fmt"

// Returns nil if the rule does not match.
type Rule func(*Machine, Expression) Expression

type Machine struct {
	Trace bool

	dupCount int64
	rules    []Rule // TODO: map[string]ReduceFunc
}

func (vm *Machine) FreshDupLabel() int64 {
	vm.dupCount++
	return vm.dupCount
}

// TODO: Integrate with Reduce; utilize parallism; avoid Go's stack.
func (vm *Machine) Normalize(x *Expression) (changed bool) {
	loop := true
	for loop {
		if vm.Trace {
			fmt.Println("Normalizing:")
			DumpExpression(*x)
		}
		y := (*x).Reduce(vm)
		loop = *x != y
		*x = y

		switch x := (*x).(type) {
		case *ConsExpr:
			for i := range x.Args {
				loop = loop || vm.Normalize(&x.Args[i])
			}

		case *LetExpr:
			for i := range x.Inits {
				loop = loop || vm.Normalize(&x.Inits[i])
			}
			loop = loop || vm.Normalize(&x.Cont.X)

		case *DupExpr:
			loop = loop || vm.Normalize(&x.Init)
			loop = loop || vm.Normalize(&x.Cont.X)

		case *AppExpr:
			loop = loop || vm.Normalize(&x.Func)
			loop = loop || vm.Normalize(&x.Arg)

		case *LamExpr:
			loop = loop || vm.Normalize(&x.Cont.X)

		case *Op2Expr:
			loop = loop || vm.Normalize(&x.A)
			loop = loop || vm.Normalize(&x.B)

		case *VarExpr:
			if x.X != nil {
				loop = loop || vm.Normalize(&x.X)
			}

		case *LitExpr, *SupExpr, *EraseExpr:
			// No-op.

		default:
			panic(fmt.Errorf("cannot normalize %T", x))
		}

		changed = changed || loop
	}
	if vm.Trace {
		fmt.Println("Normalized:")
		DumpExpression(*x)
	}
	return
}

func (vm *Machine) AddRule(rule Rule) {
	vm.rules = append(vm.rules, rule)
}

func (vm *Machine) free(x Expression) {
	if vm.Trace {
		fmt.Println("free:")
		DumpExpression(x)
	}
	// The Go garbage collector will do the actual freeing.
}
