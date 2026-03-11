def somePropExpr : MetaM Expr := do
  let funcType ← mkArrow (.const ``Nat []) (.const ``Nat [])
  withLocalDecl `f BinderInfo.default funcType fun f => do
    let feqn ← withLocalDecl `n BinderInfo.default (.const ``Nat []) fun n => do
      let lhs := .app f n
      let rhs := .app f (← mkAppM ``Nat.succ #[n])
      let eqn ← mkEq lhs rhs
      mkForallFVars #[n] eqn
    mkLambdaFVars #[f] feqn

#check someProp
-- fun f => ∀ (n : Nat), f n = f (Nat.succ n) : (Nat → Nat) → Prop
#reduce someProp Nat.succ
-- ∀ (n : Nat), Nat.succ n = Nat.succ (Nat.succ n)
