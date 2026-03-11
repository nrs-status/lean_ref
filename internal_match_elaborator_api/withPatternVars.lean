import Lean

open Lean Elab Term

def myview : TermElabM TermMatchAltView := do .pure {
  ref := <- `(Nat.succ (Nat.succ Nat.zero))
  patterns := #[<- `(Nat.succ y), <- `(Prod.mk x z)]
  lhs := .missing
  rhs := .mk .missing }

def mycollecting := show TermElabM _ from 
  do 
    collectPatternVars (<- myview)

def mytesting : TermElabM Unit := do
  let alt <- myview
  withRef alt.ref do
    let (patternVars, alt) <- mycollecting
    withPatternVars patternVars fun patternVarDecls =>
      dbg_trace (patternVarDecls.map PatternVarDecl.fvarId).map FVarId.name
      .pure .unit
      

/-- info: #[_uniq.2894, _uniq.2897, _uniq.2900] -/
#guard_msgs in
#eval mytesting
