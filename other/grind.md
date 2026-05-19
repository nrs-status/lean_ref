- The general idea behind `grind`: `grind` keeps two sets of propositions, which are in fact two equivalence classes: True and False. When called, `grind` begins by adding the desired goal to the `False` set and the available hypotheses to the `True` set. `grind`'s engines extend the `True` and `False` sets, and it succeeds when it finds an intersection between them, which means it found a contradiction.
- The e-matching engine is one of `grind`'s engines. It consists of a table whose indexes are patterns and whose values are theorems. Given
```
theorem gf (x : Nat) : g (f x) = x := by
  simp [f, g]
```
the command `grind_pattern gf => g (f x)` (which is the desugaring of the attribute `@[grind =]`) tells the e-matching engine to add, at index `g (f x)`, the theorem `gf`. When grind finds `g (f x)` in the `True` set or the `False` sets, it will call the theorem `gf` to add `x` to that set. 

- You can use `[grind? =]` for any grind attribute to see what entry it adds to the e-matching engine's table.
- `trace.grind.assert` tracks extensions to the True/False sets. To see which engine extended the sets, you need to use the engine-specific traces:
  - `trace.grind.ematch.instance` for the e-matching engine
  - `trace.grind.eqc` for the constraint propagation engine
  - etc.
