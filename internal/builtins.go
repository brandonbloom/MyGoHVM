package internal

var Add = Operator{
	Name: "Add",
	Func: func(a, b Value) Value {
		return a.(int) + b.(int)
	},
}

var Mul = Operator{
	Name: "Mul",
	Func: func(a, b Value) Value {
		return a.(int) * b.(int)
	},
}

func IsNil(x Expression) bool {
	cons, ok := x.(*ConsExpr)
	return ok && cons.Ctor == "Nil" && len(cons.Args) == 0
}

func MatchPair(x Expression) (left, right Expression, ok bool) {
	pair, ok := x.(*ConsExpr)
	if !(ok && len(pair.Args) == 2) {
		return nil, nil, false
	}
	return pair.Args[0], pair.Args[1], true
}
