import Lean
import Batteries.Tactic.OpenPrivate

open Lean Meta
open private envExtensionsRef from Lean.Environment

abbrev ref := envExtensionsRef -- these are nameless but they are indexed, maybe it has more extensions than persistentEnvExtensionsRef?
abbrev persref := persistentEnvExtensionsRef

def printPersExts : CoreM Unit := do
  for elm in (<- persref.get) do
    println! elm.name
#eval printPersExts
