open Lean Meta Elab Tactic

-- MessageData string interpolation
example {α} (a : α) (f : α → α) (h : ∀ a, f a = a) : f (f a) = a := by
  run_tac
    let g ← getMainDecl
    logInfo m!"the type is {g.type}"
