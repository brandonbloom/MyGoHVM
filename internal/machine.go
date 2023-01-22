package internal

import "fmt"

// Returns nil if the rule does not match.
type Rule func(*Machine, Expression) Expression

type Machine struct {
	Trace bool

	dupCount int64
	rules    []Rule           // TODO: map[string]ReduceFunc or map[string][arity: int]ReduceFunc.
	todo     map[Frame]*Frame // References interned by value.
}

func NewMachine() *Machine {
	return &Machine{
		todo: make(map[Frame]*Frame),
	}
}

type Frame struct {
	Parent *Frame
	X      *Expression
}

func (vm *Machine) FreshDupLabel() int64 {
	vm.dupCount++
	return vm.dupCount
}

func (vm *Machine) Normalize(x Expression) Expression {
	frame := vm.enqueueChild(nil, &x)
	vm.run()
	return *frame.X
}

func (vm *Machine) run() {
	for {
		frame := vm.dequeue()
		if frame == nil {
			break
		}
		x := *frame.X
		if vm.Trace {
			fmt.Println("reducing:")
			DumpExpression(x)
		}
		y := x.Reduce(vm)
		if vm.Trace {
			fmt.Println("reduced:")
			DumpExpression(y)
		}
		if x != y {
			*frame.X = y
			vm.enqueueFrame(frame)
			if frame.Parent != nil {
				vm.enqueueFrame(frame.Parent)
			}
		}
		y.TraverseChildren(func(child *Expression) {
			vm.enqueueChild(frame, child)
		})
	}
}

func (vm *Machine) enqueueFrame(frame *Frame) {
	key := *frame
	vm.todo[key] = frame
}

func (vm *Machine) enqueueChild(parent *Frame, x *Expression) *Frame {
	key := Frame{
		Parent: parent,
		X:      x,
	}
	frame, exists := vm.todo[key]
	if !exists {
		frame = &key
		vm.todo[key] = frame
	}
	if vm.Trace {
		fmt.Printf("enqueue %p with parent=%p expression:\n", frame, frame.Parent)
		DumpExpression(*frame.X)
	}
	return frame
}

func (vm *Machine) dequeue() *Frame {
	for key, frame := range vm.todo {
		delete(vm.todo, key)
		return frame
	}
	return nil
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
