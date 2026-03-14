import Lean
import Qq

open Qq
open Lean

#eval show MetaM Unit from do
  let u : Level := .param `u
  withLocalDeclDQ `α q(Sort u) fun α =>
  withLocalDeclDQ `x q($α) fun x =>
  withLocalDeclDQ `y q($α) fun y =>
  withLocalDeclDQ `eq q($x = $y) fun eq => do
    let lctx <- getLCtx
    let xdecl := lctx.getFromUserName! `x
    let eqdecl := lctx.getFromUserName! `eq
    let o <- findLocalDeclDependsOn eqdecl (fun fvarid => fvarid == xdecl.fvarId)
    dbg_trace o
/--
info: true
-/
