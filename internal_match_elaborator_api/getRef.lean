import Lean

open Lean Elab Term

def mytesting : TermElabM Unit := do
  withRef (<- `(Nat.succ y)) <| do
    let x <- getRef
    dbg_trace x

/--
info: (Term.app
 `Nat.succ._@.Macroexpander.garden.1843219765._hygCtx._hyg.2
 [`y._@.Macroexpander.garden.1843219765._hygCtx._hyg.2])
-/
#guard_msgs in
#eval mytesting
