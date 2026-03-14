import Lean
import Qq
import Batteries.Tactic.OpenPrivate

open private generalize from Lean.Elab.Match

open Qq
open Lean Meta Elab Term

deriving instance Repr for FVarIdSet

def myview1 : TermElabM TermMatchAltView := do .pure {
  ref := <- `(`x)
  patterns := #[<- `(Bool.true)]
  lhs := <- `(`y)
  rhs := <- `(ifTrue h) }

def myview2 : TermElabM TermMatchAltView := do .pure {
  ref := <- `(`x)
  patterns := #[<- `(Bool.false)]
  lhs := <- `(`y)
  rhs := <- `(ifFalse h) }

deriving instance Repr for Discr


#eval show TermElabM Unit from do
  let u : Level := .param `u
  withLocalDeclDQ `α q(Sort u) fun α =>
  withLocalDeclDQ `b q(Bool) fun b =>
  withLocalDeclDQ `ifTrue q($b = true -> $α) fun ifTrue => 
  withLocalDeclDQ `ifFalse q($b = false -> $α) fun ifFalse => do
    let discrs := #[Discr.mk b (.some (.atom .none "h"))]
    let r <- generalize 
      discrs
      q(Bool -> $α) 
      #[<- myview1, <- myview2]
      .none
    dbg_trace repr b.fvarId!
    dbg_trace repr ifTrue.fvarId!
    dbg_trace repr ifFalse.fvarId!
    dbg_trace repr r.discrs
    dbg_trace repr r.toClear
    dbg_trace repr r.refined
    dbg_trace (<- Lean.PrettyPrinter.ppExpr r.matchType)
    let altviews := r.altViews
    for view in altviews do
      dbg_trace view.patterns.map Lean.Syntax.prettyPrint

/--
info: Lean.Name.mkNum `_uniq 7165
Lean.Name.mkNum `_uniq 7166
Lean.Name.mkNum `_uniq 7167
#[{ expr := Lean.Expr.fvar (Lean.Name.mkNum `_uniq 7165), h? := some (Lean.Syntax.atom (Lean.SourceInfo.none) "h") },
  { expr := Lean.Expr.fvar (Lean.Name.mkNum `_uniq 7166), h? := none },
  { expr := Lean.Expr.fvar (Lean.Name.mkNum `_uniq 7167), h? := none }]
#[Lean.Name.mkNum `_uniq 7166, Lean.Name.mkNum `_uniq 7167]
true
(a : Bool) → (a = true → α) → (a = false → α) → α
#[ Bool.true ,  ifTrue ,  ifFalse ]
#[ Bool.false ,  ifTrue ,  ifFalse ]
-/

