```
macro_rules
| `(_%$h + _%$h') => `(5 + _%$h')
| `(1 + _%$h) => `(456)

/--
error: don't know how to synthesize placeholder
context:
⊢ Nat
-/
#guard_msgs in
#eval _ + _

/-- info: 456 -/
#guard_msgs in
#eval 1 + _
```
