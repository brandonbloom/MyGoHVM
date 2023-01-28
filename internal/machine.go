package internal

import (
	"fmt"
	"os"
	"sync"
	"sync/atomic"
)

// Returns nil if the rule does not match.
type Rule func(*Machine, *ConsExpr) Expression

type Machine struct {
	Trace bool

	dupCount int64
	rules    map[string]Rule // TODO: Further optimize dispatch by arity.
}

func NewMachine() *Machine {
	return &Machine{
		rules: make(map[string]Rule),
	}
}

func (vm *Machine) FreshDupLabel() int64 {
	vm.dupCount++
	return vm.dupCount
}

func (vm *Machine) Normalize(x Expression) Expression {
	_ = vm.normalize(&x)
	return x
}

func (vm *Machine) normalize(e *Expression) (changed bool) {
	x := *e
	for {
		y := x.Reduce(vm)
		if x != y {
			x = y
			changed = true
			continue
		}
		var childrenChanged atomic.Bool
		var wg sync.WaitGroup
		x.TraverseChildren(func(child *Expression) {
			wg.Add(1)
			go func() {
				if childChanged := vm.normalize(child); childChanged {
					childrenChanged.Store(true)
				}
				wg.Done()
			}()
		})
		wg.Wait()
		if childrenChanged.Load() {
			changed = true
		} else {
			*e = x
			return changed
		}
	}
}

func (vm *Machine) AddRule(ctor string, rule Rule) {
	if _, exists := vm.rules[ctor]; exists {
		fmt.Fprintf(os.Stderr, "warning: overriding %s rule\n", ctor)
	}
	vm.rules[ctor] = rule
}

func (vm *Machine) free(x Expression) {
	if vm.Trace {
		fmt.Println("free:")
		DumpExpression(x)
	}
	// The Go garbage collector will do the actual freeing.
}
