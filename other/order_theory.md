1. A function f is monotone if a ≤ b implies f a ≤ f b.
Abramsky
2. Poset: a set equipped with a relation that is reflexive, transitive, and antisymmetric. Also called a partially ordered set.
3. A subset X of a poset P is directed := X is nonempty and each pair in X has an upper bound in X.
4. A subset X of a poset P is a chain := X is nonempty and totally ordered
Mathlib
5. OmegaCompletePartialOrder.Chain : a function (f : Nat -> A) s.t. n ≤ m -> f n ≤ f m
6. OmegaCompletePartialOrder: a partial order where every OmegaCompletePartialOrder.Chain has a supremum. This is represented by a function (wSup : Chain A -> A)
7. OmegaCompletePartialOrder.ContinuousHom : a function (f : A -> B) s.t.
   i. It is monotone, i.e.: a ≤ a' -> f a ≤ f a'
   ii. for any chain (c : Chain A), f (wSup c) = wSup (c.map f); i.e. it preserves the wSup
8. instances: 
