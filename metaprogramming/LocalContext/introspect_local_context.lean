import Lean

open Lean Elab 

def printLocalDeclUserNamesAndTypes : TermElabM Unit := do
  let lctx <- getLCtx
  let e := lctx.decls.map (fun decl => match decl with
    | .some x => Option.some (x.userName, x.type)
    | .none => Option.none)
  dbg_trace e.toArray


