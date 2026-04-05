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
