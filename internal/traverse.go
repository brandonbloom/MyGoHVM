package internal

/*
func PostOrder(x *Expression, f func(*Expression)) {
	(*x).TraverseChildren(func(child *Expression) {
		PostOrder(child, f)
		f(child)
	})
	f(x)
}
*/

func (x *LitExpr) TraverseChildren(f func(*Expression)) {
	// No children.
}

func (x *AppExpr) TraverseChildren(f func(*Expression)) {
	f(&x.Func)
	f(&x.Arg)
}

func (x *VarExpr) TraverseChildren(f func(*Expression)) {
	if x.X != nil {
		f(&x.X)
	}
}

func (x *ConsExpr) TraverseChildren(f func(*Expression)) {
	for i := range x.Args {
		f(&x.Args[i])
	}
}

func (x *LetExpr) TraverseChildren(f func(*Expression)) {
	for i := range x.Inits {
		f(&x.Inits[i])
	}
	f(&x.Cont.X)
}

func (x *EraseExpr) TraverseChildren(f func(*Expression)) {
	f(&x.X)
	f(&x.K)
}

func (x *DupExpr) TraverseChildren(f func(*Expression)) {
	f(&x.Init)
	f(&x.Cont.X)
}

func (x *SupExpr) TraverseChildren(f func(*Expression)) {
	f(&x.A)
	f(&x.B)
}

func (x *Op2Expr) TraverseChildren(f func(*Expression)) {
	f(&x.A)
	f(&x.B)
}

func (x *LamExpr) TraverseChildren(f func(*Expression)) {
	f(&x.Cont.X)
}
