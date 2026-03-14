import Lean
import Qq

open Lean Meta Match Qq
open Lean Elab Term

#print Nat.succ
#print MkMatcherInput
def myelab (discr_stx : Syntax) : TermElabM Expr := do
  let discr <- elabTermEnsuringTypeQ discr_stx q(Nat)
  -- let discr : Expr := q(Nat.succ (Nat.succ Nat.zero))
  let matcher <- Lean.Meta.Match.mkMatcher {
    matcherName := <- mkAuxDeclName `match
    matchType := q(Nat -> Bool)
    discrInfos := #[{}]
    lhss := [
      <- withLocalDeclDQ `nn q(Nat) fun nn => return {
        ref := <- getRef
        fvarDecls := [<- nn.fvarId!.getDecl]
        patterns := [.ctor `Nat.succ [] [] [.var nn.fvarId!]]
      },
      <- withLocalDeclDQ `n q(Nat) fun n => return {
        ref := <- getRef
        fvarDecls := [<- n.fvarId!.getDecl]
        patterns := [.var n.fvarId!]
      }

    ]
  }
  matcher.addMatcher
  let motive : Q(Nat -> Type) := q(fun _ => Bool)
  let alt1 : Q(Nat -> Bool) := q(fun _ => Bool.true)
  let alt2 : Q(Nat -> Bool) := q(fun _ => Bool.false)
  .pure <| mkAppN matcher.matcher #[motive, discr, alt1, alt2]

elab "test" x:term : term => myelab x


#reduce test (Nat.succ Nat.zero)
-- true

#reduce test Nat.zero
-- false
