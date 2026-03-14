import Lean
import Qq

open Qq
open Lean Meta

deriving instance Repr for FVarIdSet

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclDQ `x q(Nat) fun x =>
  withLocalDeclDQ `eq q($x = 4) fun eq => do
    dbg_trace repr eq.fvarId!
    let o <- getFVarsToGeneralize #[x]
    let o' <- getFVarsToGeneralize #[eq]
    dbg_trace repr o
    dbg_trace repr o'

/--
info: Lean.Name.mkNum `_uniq 978
#[Lean.Name.mkNum `_uniq 978]
#[]
-/

