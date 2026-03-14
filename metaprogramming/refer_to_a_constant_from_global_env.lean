import Lean

open Lean

def b : Bool := .true
#eval show CoreM Unit from do
  let myenv <- getEnv
  let .some x := myenv.find? `b | throwError "notfound"
  dbg_trace x.type

