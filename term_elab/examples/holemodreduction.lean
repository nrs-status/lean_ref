syntax (name := holeModReduction) "_r" : term
open Lean Elab Term
@[term_elab holeModReduction]
def holeModReductionElab : TermElab := fun _ expectedType? => do
  let .some expectedType := expectedType? | throwError "no expected type"
  let reducedExpectedType <- Lean.Meta.reduce expectedType true false true
  let w_pp <- Lean.PrettyPrinter.ppExpr reducedExpectedType
  logInfo w_pp
  let hole <- elabTerm (<- `(_)) expectedType
  .pure hole
