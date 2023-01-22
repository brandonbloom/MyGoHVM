package internal

var Add = Operator{
	Name: "Add",
	Func: func(a, b Value) Value {
		return a.(int) + b.(int)
	},
}
