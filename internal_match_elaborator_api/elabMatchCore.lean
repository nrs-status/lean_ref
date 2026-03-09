import Lean
import Batteries.Tactic.OpenPrivate
import Qq

open Qq

open Lean Elab

open private elabMatchCore from Lean.Elab.Match

def my_match_stx : CoreM Syntax := `(match Prod.mk Nat.zero Nat.zero with | Prod.mk x y => y)

/--
info: match (Nat.zero, Nat.zero) with
| (x, y) => y
-/
#guard_msgs in
#eval show TermElabM Unit from do
  let r <- elabMatchCore (<- my_match_stx) <| .some q(Nat)
  dbg_trace (<- Lean.PrettyPrinter.ppExpr r)


def my_match_stxa : CoreM Syntax := `(match (7 : Nat) with | .zero => "iszero" | .succ nn => "isnotzero")

/--
info: match 7 with
| Nat.zero => "iszero"
| nn.succ => "isnotzero"
-/
#guard_msgs in
#eval show TermElabM Unit from do
  let r <- elabMatchCore (<- my_match_stxa) <| .some q(String)
  dbg_trace (<- Lean.PrettyPrinter.ppExpr r)
