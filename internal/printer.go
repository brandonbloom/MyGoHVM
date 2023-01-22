package internal

import (
	"fmt"
	"io"
	"os"
)

type Printer struct {
	w              io.Writer
	nameCounts     map[string]int   // Number of unique vars with a given name.
	discriminators map[*VarExpr]int // Maps vars to name count at time first seen.
	counter        int64
}

func NewPrinter(w io.Writer) *Printer {
	return &Printer{
		w:              w,
		nameCounts:     map[string]int{},
		discriminators: map[*VarExpr]int{},
	}
}

func DumpExpression(x Expression) {
	printer := NewPrinter(os.Stdout)
	x.Visit(printer)
	fmt.Println()
}

func (printer *Printer) discriminate(v *VarExpr) int {
	discriminator, ok := printer.discriminators[v]
	if !ok {
		discriminator = printer.nameCounts[v.Name]
		printer.nameCounts[v.Name] = discriminator + 1
		printer.discriminators[v] = discriminator
	}
	return discriminator
}

func (printer *Printer) visitHole(v *VarExpr) {
	_ = printer.discriminate(v)
	v.Visit(printer)
}

func (printer *Printer) printf(format string, v ...interface{}) {
	_, _ = fmt.Fprintf(printer.w, format, v...)
}

func (printer *Printer) VisitVar(v *VarExpr) {
	discriminator := printer.discriminate(v)
	if discriminator == 0 {
		printer.printf("%s", v.Name)
	} else {
		printer.printf("%s#%d", v.Name, discriminator)
	}
	if v.X != nil {
		printer.printf("@")
		v.X.Visit(printer)
	}
}

func (printer *Printer) VisitCons(cons *ConsExpr) {
	if len(cons.Args) == 0 {
		printer.printf("%s", cons.Ctor)
	} else {
		printer.printf("(")
		printer.printf("%s", cons.Ctor)
		for _, arg := range cons.Args {
			printer.printf(" ")
			arg.Visit(printer)
		}
		printer.printf(")")
	}
}

func (printer *Printer) VisitApp(app *AppExpr) {
	printer.printf("(")
	app.Func.Visit(printer)
	printer.printf(" ")
	app.Arg.Visit(printer)
	printer.printf(")")
}

func (printer *Printer) VisitDup(dup *DupExpr) {
	printer.printf("#dup[%d ", dup.Label)
	printer.visitHole(dup.Cont.Holes[0])
	printer.printf(" ")
	printer.visitHole(dup.Cont.Holes[1])
	printer.printf(" ")
	dup.Init.Visit(printer)
	printer.printf(" ")
	dup.Cont.X.Visit(printer)
	printer.printf("]")
}

func (printer *Printer) VisitSup(sup *SupExpr) {
	printer.printf("#sup[%d ", sup.Label)
	sup.A.Visit(printer)
	printer.printf(" ")
	sup.B.Visit(printer)
	printer.printf("]")
}

func (printer *Printer) VisitLet(let *LetExpr) {
	printer.printf("(let {")
	sep := ""
	for i, hole := range let.Cont.Holes {
		printer.printf(sep)
		printer.visitHole(hole)
		printer.printf(" ")
		let.Inits[i].Visit(printer)
		sep = ", "
	}
	printer.printf("} ")
	let.Cont.X.Visit(printer)
	printer.printf(")")
}

func (printer *Printer) VisitErase(erase *EraseExpr) {
	printer.printf("(erase ")
	erase.X.Visit(printer)
	printer.printf(" ")
	erase.K.Visit(printer)
	printer.printf(")")
}

func (printer *Printer) VisitLit(lit *LitExpr) {
	switch v := lit.Value.(type) {
	case int:
		printer.printf("%d", v)
	case string:
		printer.printf("%q", v)
	default:
		printer.printf("<%v>", v)
	}
}

func (printer *Printer) VisitLam(lam *LamExpr) {
	printer.printf("(lam ")
	printer.visitHole(lam.Cont.Holes[0])
	printer.printf(" ")
	lam.Cont.X.Visit(printer)
	printer.printf(")")
}

func (printer *Printer) VisitOp2(op2 *Op2Expr) {
	printer.printf("(op2 %v ", op2.Op.Name)
	op2.A.Visit(printer)
	printer.printf(" ")
	op2.B.Visit(printer)
	printer.printf(")")
}
