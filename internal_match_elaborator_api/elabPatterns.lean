import Lean
import Batteries.Tactic.OpenPrivate
import Qq

open Qq

open Lean Elab Term

open private elabMatchAltView withElaboratedLHS elabPatterns from Lean.Elab.Match

/--
(#[[mdata _patWithRef: 
  ([mdata _patWithRef: Nat.succ]) 
  ([mdata _patWithRef: ?_uniq.3133])]], Nat)
(#[[mdata _patWithRef: 
  ([mdata _patWithRef: Eq.refl.{?_uniq.3134}]) 
  ?_uniq.3135 
  ([mdata _patWithRef: ?_uniq.3136])]], 
    Eq.{1} 
      Nat 
      (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)) 
      (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)))
(#[[mdata _patWithRef: 
  ([mdata _patWithRef: Nat.succ]) 
  ([mdata _patWithRef: ?_uniq.3137])], 
    [mdata _patWithRef: 
      ([mdata _patWithRef: Nat.succ]) 
      ([mdata _patWithRef: ?_uniq.3138])]], Nat)
-/

#eval show TermElabM Unit from do
  let mypat <- `(Nat.succ _)
  let xexcept <- elabPatterns #[mypat] 1 q(Nat -> Nat)
  let r <- ofExcept <| xexcept.mapError PatternElabException.ex
  dbg_trace r
  let mypat' <- `(Eq.refl _)
  let xexcept' <- elabPatterns #[mypat'] 1 q(2 + 2 = 4 -> 4 = 4)
  let r' <- ofExcept <| xexcept'.mapError PatternElabException.ex
  dbg_trace r'
  let xexcept'' <- elabPatterns #[mypat, mypat] 2 q(Nat -> Nat -> Nat)
  let r'' <- ofExcept <| xexcept''.mapError PatternElabException.ex
  dbg_trace r''
