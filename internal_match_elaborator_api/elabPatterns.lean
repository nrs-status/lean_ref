import Lean
import Batteries.Tactic.OpenPrivate
import Qq

open Qq

open Lean Elab Term

open private elabMatchAltView withElaboratedLHS elabPatterns from Lean.Elab.Match

def myexpr1 : Expr := .forallE `x q(Nat) q(Nat) .default

def myexpr2 : Expr := .forallE `p q(2 + 2 = 4) q(4 = 4) .default

/--
info: (#[
  [mdata _patWithRef: 
    ([mdata _patWithRef: Nat.succ]) 
    ([mdata _patWithRef: ?_uniq.2764])]], Nat)
(#[
  [mdata _patWithRef: 
    ([mdata _patWithRef: Eq.refl.{?_uniq.2765}]) 
    ?_uniq.2766 
    ([mdata _patWithRef: ?_uniq.2767])]], 
  Eq.{1} 
    Nat 
    (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)) 
    (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)))
-/
#eval show TermElabM Unit from do
  let mypat <- `(Nat.succ _)
  let xexcept <- elabPatterns #[mypat] 1 myexpr1
  let r <- ofExcept <| xexcept.mapError PatternElabException.ex
  dbg_trace r
  let mypat' <- `(Eq.refl _)
  let xexcept' <- elabPatterns #[mypat'] 1 myexpr2
  let r' <- ofExcept <| xexcept'.mapError PatternElabException.ex
  dbg_trace r'
