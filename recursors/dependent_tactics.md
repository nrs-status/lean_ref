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
- https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/why.20does.20.60rewrite.20at.60.20create.20a.20new.20variable.3F/with/557897686 : why does `rewrite at` sometimes duplicate the target? This is because, if the target occurs in the goal, then the result of a rewrite no long is the same term as the one occuring in the goal. For example:
```
example (n : Nat) (p : Nat -> Prop) (q : ∀n, p n -> Prop) (h : p n) (k : Nat) (eq : n = k) : q n h := by
  rw [eq] at h
  skip
```
before the rewrite, the goal is `|- q n (h : p n)`, and the rewrite duplicates the `h` hypothesis, such that the original hypothesis is renamed and its occurence in the goal is renamed accordingly. This is because a rewrite is a cast according to an equality, and therefore the type of the result of the rewrite is `eq ▸ p n`, which is not the same proposition as the one occuring in the goal.
