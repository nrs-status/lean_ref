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
info: #[`y._@.Macroexpander.garden2.3384536090._hygCtx._hyg.2, `x._@.Macroexpander.garden2.3384536090._hygCtx._hyg.2, `z._@.Macroexpander.garden2.3384536090._hygCtx._hyg.2]
true
false
true
true
-/
#guard_msgs in
#eval show TermElabM Unit from do
  let r <- mycollecting
  let v <- myview
  dbg_trace r.1
  dbg_trace r.2.ref == v.ref
  dbg_trace r.2.patterns == v.patterns
  dbg_trace r.2.lhs == v.lhs
  dbg_trace r.2.rhs == v.lhs

