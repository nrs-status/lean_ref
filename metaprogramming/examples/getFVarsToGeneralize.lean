import Lean
import Qq

open Qq
open Lean Meta

deriving instance Repr for FVarIdSet

#eval show MetaM Unit from do
  withLocalDeclDQ `x q(Nat) fun x =>
  withLocalDeclDQ `eq q($x = 4) fun eq => do
    dbg_trace repr eq.fvarId!
    let o <- getFVarsToGeneralize #[x]
    let o' <- getFVarsToGeneralize #[eq]
    let o'' <- getFVarsToGeneralize #[eq, x]
    dbg_trace repr o
    dbg_trace repr o'
    dbg_trace repr o''

/--
info: Lean.Name.mkNum `_uniq 978
#[Lean.Name.mkNum `_uniq 978]
#[]
#[]
-/

#eval show MetaM Unit from do
  let u : Level := .param `u
  withLocalDeclDQ `α q(Sort u) fun α =>
  withLocalDeclDQ `b q(Bool) fun b =>
  withLocalDeclDQ `ifTrue q($b = true -> $α) fun ifTrue => 
  withLocalDeclDQ `ifFalse q($b = true -> $α) fun ifFalse => do
    let x <- getFVarsToGeneralize #[b]
    dbg_trace repr ifTrue.fvarId!
    dbg_trace repr ifFalse.fvarId!
    dbg_trace repr x

/--
info: Lean.Name.mkNum `_uniq 18982
Lean.Name.mkNum `_uniq 18983
#[Lean.Name.mkNum `_uniq 18982, Lean.Name.mkNum `_uniq 18983]
-/



