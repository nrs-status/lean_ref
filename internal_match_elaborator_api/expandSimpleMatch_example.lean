import Lean.Parser
import Batteries.Tactic.OpenPrivate
import Lean.Elab
import Qq

open Qq
open Lean Parser Term
open Lean Elab Util

open private expandSimpleMatch from Lean.Elab.Match

def my_match_stx : CoreM Syntax := `(match Prod.mk 1 2 with | x => x.fst)

def myelab : TermElabM Unit := do
  match <- my_match_stx with
  | `(match $discr:term with | $y:ident => $rhs) => 
    let expanded <- expandSimpleMatch (<- my_match_stx) discr y rhs <| .some (.const ``Nat [])
    dbg_trace (<- Lean.PrettyPrinter.ppExpr expanded)
    .pure .unit
  | _ => throwError "nomatch"
#eval myelab
