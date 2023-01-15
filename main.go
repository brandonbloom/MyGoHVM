package main

// See https://github.com/Kindelia/HVM/blob/master/guide/HOW.md

type Value int
type Variable int
type Symbol int
type Expression int
type Operation func(a, b Value) Value

type Rules interface {
	/*
		dup x y = N
		-----------
		x <- N
		y <- N
	*/
	DupVal(x, y Variable, value Value)

	/*
		dup x y = (Foo a b ...)
		----------------------- Dup-Ctr
		dup a0 a1 = a
		dup b0 b1 = b
		...
		x <- (Foo a0 b0 ...)
		y <- (Foo a1 b1 ...)
	*/
	DupCtr(x, y Variable, head Symbol, body []Expression)

	/*
		(λx(body) arg)
		-------------- App-Lam
		x <- arg
		body
	*/
	AppLam(x Variable, body Expression, arg Expression)

	/*
		dup a b = λx(body)
		------------------ Dup-Lam
		a <- λx0(b0)
		b <- λx1(b1)
		x <- {x0 x1}
		dup b0 b1 = body
	*/
	DupLam(a, b Variable, x Variable, body Expression)

	/*
		For a Dup-Sup that represents the end of a duplication process.

		dup a b = {r s}
		--------------- Dup-Sup
		a <- r
		b <- s
	*/
	DupSupEnd(a, b Variable, r, s Expression)

	/*
		For duplicating a term, which itself duplicates something.

		dup x y = {a b}
		--------------- Dup-Sup (different)
		x <- {xA xB}
		y <- {yA yB}
		dup xA yA = a
		dup xB yB = b
	*/
	DupSupRec(a, b Variable, r, s Expression)

	/*
		({a b} c)
		--------------- App-Sup
		dup x0 x1 = c
		{(a x0) (b x1)}
	*/
	AppSup(a, b Expression, c Expression)

	/*
		(+ {a0 a1} b)
		--------------------- Op2-Sup-A
		dup b0 b1 = b
		{(+ a0 b0) (+ a1 b1)}
	*/
	Op2SupA(op Operation, a0, a1 Expression, b Expression)

	/*
		(+ a {b0 b1})
		--------------------- Op2-Sup-B
		dup a0 a1 = a
		{(+ a0 b0) (+ a1 b1)}
	*/
	Op2SupB(op Operation, a Expression, b0, b1 Expression)
}

func main() {
}
