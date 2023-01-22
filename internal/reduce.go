package internal

func (erase *EraseExpr) Reduce(vm *Machine) Expression {
	vm.free(erase.X)
	return erase.K
}

func (v *VarExpr) Reduce(vm *Machine) Expression {
	if v.X == nil {
		return v
	}
	return v.X
}

func (op2 *Op2Expr) Reduce(vm *Machine) Expression {
	// (Op2 f a b) = ...
	if a, ok := op2.A.(*LitExpr); ok {
		if b, ok := op2.B.(*LitExpr); ok {
			return Lit(op2.Op.Func(a.Value, b.Value))
		}
	}

	/*
	  (+ {a0 a1} b)
	  --------------------- Op2-Sup-A
	  dup b0 b1 = b
	  {(+ a0 b0) (+ a1 b1)}
	*/
	if sup, ok := op2.A.(*SupExpr); ok {
		b := op2.B
		op := op2.Op
		a0 := sup.A
		a1 := sup.B
		return Dup(sup.Label, "b0", "b1", b, func(b0, b1 *VarExpr) Expression {
			return Sup(sup.Label, Op2(op, a0, b0), Op2(op, a1, b1))
		})
	}

	/*
		(+ a {b0 b1})
		--------------------- Op2-Sup-B
		dup a0 a1 = a
		{(+ a0 b0) (+ a1 b1)}
	*/
	if sup, ok := op2.B.(*SupExpr); ok {
		a := op2.A
		op := op2.Op
		b0 := sup.A
		b1 := sup.B
		return Dup(sup.Label, "a0", "a1", a, func(a0, a1 *VarExpr) Expression {
			return Sup(sup.Label, Op2(op, a0, b0), Op2(op, a1, b1))
		})
	}

	return op2
}

func (let *LetExpr) Reduce(vm *Machine) Expression {
	// (Let {x init, ...} body) => ...
	return let.Cont.FillHoles(let.Inits...)
}

func (dup *DupExpr) Reduce(vm *Machine) Expression {

	switch init := dup.Init.(type) {
	case *LitExpr:
		lit := init
		/*
			(Dup a b (Lit ...) k)
			---------------------
			(k a b ...)
		*/
		return dup.Cont.FillHoles(lit, lit)

	case *ConsExpr:
		cons := init
		/*
			(Dup a b (Cons ctor args...) k)
			----------------------------- Dup-Cons
			dup a0 a1 = a
			dup b0 b1 = b
			...
			(k (Foo a0 b0 ...) (Foo a1 b1 ...))
		*/
		arity := len(cons.Args)
		argsA := make([]Expression, arity)
		argsB := make([]Expression, arity)
		exprs := make([]Expression, arity+1)
		res := &LetExpr{
			Cont: dup.Cont,
		}
		exprs[arity] = res
		for i := arity - 1; i >= 0; i-- {
			argA := &VarExpr{Name: "argA"}
			argB := &VarExpr{Name: "argB"}
			argsA[i] = argA
			argsB[i] = argB
			exprs[i] = &DupExpr{
				Label: dup.Label,
				Init:  cons.Args[i],
				Cont: Continuation{
					X: exprs[i+1],
					Holes: []*VarExpr{
						argA,
						argB,
					},
				},
			}
		}
		res.Inits = []Expression{
			&ConsExpr{cons.Ctor, argsA},
			&ConsExpr{cons.Ctor, argsB},
		}
		return exprs[0]

	case *LamExpr:
		lam := init
		/*
			(Dup a b (Lam param body) k)

			dup a b = λx(body)
			------------------ Dup-Lam
			a <- λx0(b0)
			b <- λx1(b1)
			x <- {x0 x1}
			dup b0 b1 = body
		*/
		arg0 := Var("arg0")
		arg1 := Var("arg1")
		sup := Sup(dup.Label, arg0, arg1)
		body := lam.Cont.FillHoles(sup)
		body0 := Var("body0")
		body1 := Var("body1")
		return &DupExpr{
			Label: dup.Label,
			Init:  body,
			Cont: Continuation{
				X: &LetExpr{
					Inits: []Expression{
						&LamExpr{
							Cont: Continuation{
								X:     body0,
								Holes: []*VarExpr{arg0},
							},
						},
						&LamExpr{
							Cont: Continuation{
								X:     body1,
								Holes: []*VarExpr{arg1},
							},
						},
					},
					Cont: dup.Cont,
				},
				Holes: []*VarExpr{body0, body1},
			},
		}

	case *SupExpr:
		sup := init
		if dup.Label == sup.Label {
			/*
				When ending the duplication process.

				dup a b = {r s}
				-------- Dup-Sup (base)
				a <- r
				b <- s
			*/
			return dup.Cont.FillHoles(sup.A, sup.B)
		} else {
			/*
				  When duplicating a term, which itself duplicates something.

					dup x y = {a b}
					--------- Dup-Sup (recur)
					x <- {xA xB}
					y <- {yA yB}
					dup xA yA = a
					dup xB yB = b
			*/
			return Dup(dup.Label, "xA", "yA", sup.A, func(xA, yA *VarExpr) Expression {
				return Dup(dup.Label, "xB", "yB", sup.B, func(xB, yB *VarExpr) Expression {
					x := Sup(dup.Label, xA, xB)
					y := Sup(dup.Label, yA, yB)
					return dup.Cont.FillHoles(x, y)
				})
			})
		}
	}

	return dup
}

func (app *AppExpr) Reduce(vm *Machine) Expression {
	/*
		(λx(body) arg)
		-------------- App-Lam
		x <- arg
		body
	*/
	if lam, ok := app.Func.(*LamExpr); ok {
		return lam.Cont.FillHoles(app.Arg)
	}

	return app
}

func (sup *SupExpr) Reduce(vm *Machine) Expression {
	return sup
}

func (lit *LitExpr) Reduce(vm *Machine) Expression {
	return lit
}

func (lam *LamExpr) Reduce(vm *Machine) Expression {
	return lam
}

func (cons *ConsExpr) Reduce(vm *Machine) Expression {
	for _, rule := range vm.rules {
		redex := rule(vm, cons)
		if redex != nil {
			return redex
		}
	}
	return cons
}
