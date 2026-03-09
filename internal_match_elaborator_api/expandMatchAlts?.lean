import Lean.Elab

open Lean Elab Term

def my_match_stx : CoreM Syntax := `(match x with 
  | y | k => h)

#eval show TermElabM Unit from do
  let r <- liftMacroM <| expandMatchAlts? (<- my_match_stx)
  dbg_trace r
