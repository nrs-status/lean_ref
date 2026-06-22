- Given the state
```
n : Nat
h : P n
|- Q n
```
the `induction n` tactic generates two states (= goals = mvar contexts)
```
h : P 0
|- Q 0
```
and
```
nn : Nat
h : P nn.succ
ih : P nn -> Q nn
|- Q nn.succ
```
