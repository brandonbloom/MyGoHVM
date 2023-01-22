package internal

import "fmt"

type Continuation struct {
	X     Expression
	Holes []*VarExpr
}

func (k Continuation) FillHoles(xs ...Expression) Expression {
	for i, x := range xs {
		k.Holes[i].X = x
	}
	return k.X
}

func makeCont(holes []string, f func(...*VarExpr) Expression) Continuation {
	vars := make([]*VarExpr, len(holes))
	for i, hole := range holes {
		vars[i] = &VarExpr{
			Name: hole,
		}
	}
	x := f(vars...)
	cb := newContBuilder(vars...)
	x.Visit(cb)
	for i, hole := range cb.holes {
		if hole == nil {
			panic(fmt.Errorf("hole not found: %s", holes[i]))
		}
	}
	return Continuation{
		X:     x,
		Holes: cb.holes,
	}
}

func makeLamCont(hole string, f func(*VarExpr) Expression) Continuation {
	return makeCont([]string{hole}, func(vars ...*VarExpr) Expression {
		return f(vars[0])
	})
}

func makeDupCont(holeA, holeB string, f func(*VarExpr, *VarExpr) Expression) Continuation {
	return makeCont([]string{holeA, holeB}, func(vars ...*VarExpr) Expression {
		return f(vars[0], vars[1])
	})
}

type contBuilder struct {
	variables []*VarExpr // Variables to find the addresses of.
	holes     []*VarExpr // Found addresses of parallel found variables.
}

func newContBuilder(variables ...*VarExpr) *contBuilder {
	return &contBuilder{
		variables: variables,
		holes:     make([]*VarExpr, len(variables)),
	}
}

func (cb *contBuilder) VisitLit(lit *LitExpr) {
	// No children.
}

func (cb *contBuilder) VisitApp(app *AppExpr) {
	app.Func.Visit(cb)
	app.Arg.Visit(cb)
}

func (cb *contBuilder) VisitVar(v *VarExpr) {
	for i, candidate := range cb.variables {
		if candidate == v {
			if cb.holes[i] != nil {
				panic(fmt.Errorf("non-linear hole: %s", v.Name))
			}
			cb.holes[i] = v
		}
	}
}

func (cb *contBuilder) VisitCons(cons *ConsExpr) {
	for i := range cons.Args {
		cons.Args[i].Visit(cb)
	}
}

func (cb *contBuilder) VisitLet(let *LetExpr) {
	for i := range let.Inits {
		let.Inits[i].Visit(cb)
	}
	let.Cont.X.Visit(cb)
}

func (cb *contBuilder) VisitErase(erase *EraseExpr) {
	erase.X.Visit(cb)
	erase.K.Visit(cb)
}

func (cb *contBuilder) VisitDup(dup *DupExpr) {
	dup.Init.Visit(cb)
	dup.Cont.X.Visit(cb)
}

func (cb *contBuilder) VisitSup(sup *SupExpr) {
	sup.A.Visit(cb)
	sup.B.Visit(cb)
}

func (cb *contBuilder) VisitOp2(op2 *Op2Expr) {
	op2.A.Visit(cb)
	op2.B.Visit(cb)
}

func (cb *contBuilder) VisitLam(lam *LamExpr) {
	lam.Cont.X.Visit(cb)
}
