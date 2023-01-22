package internal

type Value any

type Expression interface {
	Visit(Visitor)
	Reduce(*Machine) Expression
}

type LitExpr struct {
	Value Value
}

func Lit(x Value) *LitExpr {
	return &LitExpr{Value: x}
}

type VarExpr struct {
	Name string
	X    Expression
}

func Var(name string) *VarExpr {
	return &VarExpr{
		Name: name,
		X:    nil,
	}
}

type ConsExpr struct {
	Ctor string
	Args []Expression
}

func Cons(ctor string, args ...Expression) *ConsExpr {
	return &ConsExpr{
		Ctor: ctor,
		Args: args,
	}
}

type AppExpr struct {
	Func Expression
	Arg  Expression
}

func App(f Expression, x Expression) *AppExpr {
	return &AppExpr{
		Func: f,
		Arg:  x,
	}
}

type LetExpr struct {
	Inits []Expression
	Cont  Continuation
}

func LetParallel(names []string, inits []Expression, body func(v ...*VarExpr) Expression) *LetExpr {
	return &LetExpr{
		Inits: inits,
		Cont:  makeCont(names, body),
	}
}

type Binding struct {
	Name string
	Init Expression
}

func MakeBinding(name string, init Expression) Binding {
	return Binding{Name: name, Init: init}
}

func Let(bindings []Binding, body func(v ...*VarExpr) Expression) *LetExpr {
	n := len(bindings)
	names := make([]string, n)
	inits := make([]Expression, n)
	for i, binding := range bindings {
		names[i] = binding.Name
		inits[i] = binding.Init
	}
	return LetParallel(names, inits, body)
}

func Let1(name string, init Expression, body func(v *VarExpr) Expression) *LetExpr {
	return LetParallel([]string{name}, []Expression{init}, func(vars ...*VarExpr) Expression {
		return body(vars[0])
	})
}

type EraseExpr struct {
	X Expression // TODO: Variadic.
	K Expression
}

func Erase(x Expression, k Expression) *EraseExpr {
	return &EraseExpr{X: x, K: k}
}

// TODO: Variadic. type DupBinding { Name string; Count int; Init Expression }
// TODO: Represent Let and Erase as Dup count=1 and count=0 respectively?
type DupExpr struct {
	Label int64
	Init  Expression
	Cont  Continuation
}

func Dup(label int64, nameA, nameB string, init Expression, f func(*VarExpr, *VarExpr) Expression) *DupExpr {
	return &DupExpr{
		Label: label,
		Init:  init,
		Cont:  makeDupCont(nameA, nameB, f),
	}
}

type SupExpr struct {
	Label int64
	A     Expression
	B     Expression
}

func Sup(label int64, a, b Expression) *SupExpr {
	return &SupExpr{label, a, b}
}

// TODO: Variadic App of builtin?
type Op2Expr struct {
	Op Operator
	A  Expression
	B  Expression
}

type Operator struct {
	Name string
	Func func(Value, Value) Value
}

func Op2(op Operator, a, b Expression) *Op2Expr {
	return &Op2Expr{
		Op: op,
		A:  a,
		B:  b,
	}
}

// TODO: Variadic.
type LamExpr struct {
	Cont Continuation
}

func Lam(param string, body func(arg *VarExpr) Expression) *LamExpr {
	return &LamExpr{
		Cont: makeLamCont(param, body),
	}
}

type Visitor interface {
	VisitLit(*LitExpr)
	VisitApp(*AppExpr)
	VisitVar(*VarExpr)
	VisitCons(*ConsExpr)
	VisitLet(*LetExpr)
	VisitErase(*EraseExpr)
	VisitDup(*DupExpr)
	VisitSup(*SupExpr)
	VisitOp2(*Op2Expr)
	VisitLam(*LamExpr)
}

func (x *LitExpr) Visit(v Visitor)   { v.VisitLit(x) }
func (x *AppExpr) Visit(v Visitor)   { v.VisitApp(x) }
func (x *VarExpr) Visit(v Visitor)   { v.VisitVar(x) }
func (x *ConsExpr) Visit(v Visitor)  { v.VisitCons(x) }
func (x *LetExpr) Visit(v Visitor)   { v.VisitLet(x) }
func (x *EraseExpr) Visit(v Visitor) { v.VisitErase(x) }
func (x *DupExpr) Visit(v Visitor)   { v.VisitDup(x) }
func (x *SupExpr) Visit(v Visitor)   { v.VisitSup(x) }
func (x *Op2Expr) Visit(v Visitor)   { v.VisitOp2(x) }
func (x *LamExpr) Visit(v Visitor)   { v.VisitLam(x) }
