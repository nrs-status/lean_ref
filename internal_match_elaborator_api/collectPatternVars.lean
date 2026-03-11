import Lean

open Lean Elab Term

def myview : TermElabM TermMatchAltView := do .pure {
  ref := .missing
  patterns := #[<- `(Nat.succ y), <- `(Prod.mk x z)]
  lhs := .missing
  rhs := .mk .missing }

def mycollecting := show TermElabM _ from 
  do 
    collectPatternVars (<- myview)

/--
info: #[
  `y._@.Macroexpander.garden.4033628405._hygCtx._hyg.2, 
  `x._@.Macroexpander.garden.4033628405._hygCtx._hyg.2, 
  `z._@.Macroexpander.garden.4033628405._hygCtx._hyg.2]
-/
#guard_msgs in
#eval show TermElabM Unit from do
  let r <- mycollecting
  dbg_trace r.1

