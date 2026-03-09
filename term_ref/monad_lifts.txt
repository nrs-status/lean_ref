-- recall you can find instances with the batteries #instances command, see commands/find_instances.lean

MacroM to TermElabM
```
#eval show TermElabM Unit from do
  let r <- liftMacroM <| expandMatchAlts? (<- my_match_stx)
  dbg_trace r
```

CommandElabM to MetaM
```
import Lean

open Lean Parser Elab Meta Term Command

def myMetaM : MetaM Unit := do
  let addstx : Syntax <- `(def add (n : Nat) (m : Nat) : Nat := Nat.casesOn m n (fun x => add n.succ x))
  let defview <- liftCommandElabM <| mkDefView {} (addstx.setKind ``Parser.Command.definition)
  dbg_trace defview.value
  pure .unit
```
