import Lean
import Qq
import Batteries.Tactic.OpenPrivate

open private generalize elabMatchAltView from Lean.Elab.Match

open Qq
open Lean Meta Elab Term


def myview1 : TermElabM TermMatchAltView := do .pure {
  ref := <- `(`x)
  patterns := #[<- `(Bool.true)]
  lhs := <- `(`y)
  rhs := Syntax.mkApp (mkIdent `ifTrue) #[Syntax.mkApp (mkIdent `Eq.refl) #[mkHole .missing]] }

def myview2 : TermElabM TermMatchAltView := do .pure {
  ref := <- `(`x)
  patterns := #[<- `(Bool.false)]
  lhs := <- `(`y)
  rhs := <- `(ifFalse h) }

deriving instance Repr for Discr
deriving instance Repr for MatchAltView

def toeval : TermElabM Unit := do
  let u : Level := .param `u
  withLocalDeclDQ `α q(Sort u) fun α =>
  withLocalDeclDQ `b q(Bool) fun b =>
  withLocalDeclDQ `ifTrue q($b = true -> $α) fun ifTrue => 
  withLocalDeclDQ `ifFalse q($b = false -> $α) fun ifFalse => do
  let discrs := #[Discr.mk b (mkIdent `h)] 
  let matchexpr := q(Bool -> $α)
  let gen <- generalize 
    discrs
    matchexpr
    #[<- myview1, <- myview2]
    .none
  let r <- elabMatchAltView 
    gen.discrs
    gen.altViews[0]!
    gen.matchType
    #[ifTrue.fvarId!, ifFalse.fvarId!]

