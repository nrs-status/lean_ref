```
macro_rules
  | `(stx| $p +) => `(stx| many1($p))
  | `(stx| $p *) => `(stx| many($p))
  | `(stx| $p ?) => `(stx| optional($p))
  | `(stx| $p₁ <|> $p₂) => `(stx| orelse($p₁, $p₂))
  
macro:arg x:stx:max ",*"   : stx => `(stx| sepBy($x, ",", ", "))

macro:arg x:stx:max ",+"   : stx => `(stx| sepBy1($x, ",", ", "))

macro:arg x:stx:max ",*,?" : stx => `(stx| sepBy($x, ",", ", ", allowTrailingSep))

macro:arg x:stx:max ",+,?" : stx => `(stx| sepBy1($x, ",", ", ", allowTrailingSep))

macro:arg "!" x:stx:max : stx => `(stx| notFollowedBy($x))
```
located in `src/Init/Notation.lean`
