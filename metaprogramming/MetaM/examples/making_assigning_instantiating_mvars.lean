/--
?_uniq.8821
Nat.succ ?_uniq.8821
Nat.succ ?_uniq.8821
Nat.succ (OfNat.ofNat.{0} Nat 42 (instOfNatNat 42))
-/
#eval show MetaM Unit from do
  let mvar1 : Expr <- mkFreshExprMVar (mkConst `Nat)
  dbg_trace mvar1
  let e : Expr := (Lean.mkConst `Nat.succ).app mvar1
  dbg_trace e
  mvar1.mvarId!.assign (mkNatLit 42)
  dbg_trace e
  let e' : Expr <- instantiateMVars e
  dbg_trace e'

