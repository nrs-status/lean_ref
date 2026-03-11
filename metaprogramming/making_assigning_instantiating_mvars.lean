run_meta do
  let mvar1 ← mkFreshExprMVar (mkConst `Nat)
  let e := (mkConst `Nat.succ).app mvar1
  -- e is `Nat.succ ?m.773`, `?m.773` is unassigned
  mvar1.mvarId!.assign (mkNatLit 42)
  -- e is `Nat.succ ?m.773`, `?m.773` is assigned to `42`
  let e' ← instantiateMVars e
  -- e' is `Nat.succ 42`, `?m.773` is assigned to `42`
