import Lean
import Qq

open Qq
open Lean

deriving instance Repr for FVarIdSet

#eval show MetaM Unit from do
  let u : Level := .param `u
  withLocalDeclDQ `α q(Sort u) fun α =>
  withLocalDeclDQ `x q($α) fun x =>
  withLocalDeclDQ `y q($α) fun y =>
  withLocalDeclDQ `eq q($x = $y) fun eq => do
    let lctx <- getLCtx
    let o <- Lean.Meta.getFVarSetToGeneralize #[eq, x, y] {}
    dbg_trace repr eq.fvarId!
    dbg_trace repr o

/--
Lean.Name.mkNum `_uniq 16954
Std.TreeSet.ofList [Lean.Name.mkNum `_uniq 16954]
-/

