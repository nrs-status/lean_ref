```
macro_rules
  | `($f $args* <| $a) =>
    if a.raw.isMissing then
      -- Ensures that `$f $args* <|` is elaborated as `$f $args*`, not `$f $args* sorry`.
      -- For the latter, the elaborator produces `TermInfo` where the missing argument has already
      -- been applied as `sorry`, which inhibits some language server functionality that relies
      -- on this `TermInfo` (e.g. signature help).
      -- The parser will still produce an error for `$f $args* <|` in this case.
      `($f $args*)
    else
      `($f $args* $a)
  | `($f <| $a) =>
    if a.raw.isMissing then
      `($f)
    else
      `($f $a)
```
from `src/Init/Notation.lean`

some more examples i made:
```
macro_rules
| `(Nat.add $_args*) => do
  let myarray : Lean.TSyntaxArray `term := .mk #[<- `(5), <- `(10)]
  `(Nat.mul $myarray*)

/-- info: 50 -/
#guard_msgs in
#eval Nat.add 0 0
```
```
/-- info: 6 -/
#guard_msgs in
#eval show TermElabM Unit from do
  let stx <- `(x)
  let stx' <- `(y)
  let fnstx <- `(fun $[$(#[stx, stx'])]* => $stx + $stx')
  let term_for_elab <- `($fnstx 5 1)
  let x <- evalTerm Nat (<- elabTerm (<- `(Nat)) .none) term_for_elab
  dbg_trace x
```
```
macro_rules
| `(($e, $es,*)) => do
  match es.getElems.toList with
  | .cons head .nil => `(Nat.add $e $head)
  | .cons head tail => do
    let tuple <- `(($head, $(.mk tail.toArray),*)) -- Lean.Parser.Term.tuple requires stx of the form (_, _)
    `(Nat.add $e $tuple)
  | .nil => Macro.throwUnsupported

/-- info: 16 -/
#guard_msgs in
#eval (1, 5, 10)
```
