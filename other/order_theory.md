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
Gunter
8. p115: any finite poset is a cpo; the sup is the largest element of the set.
9. p116: the naturals are not a cpo; the largest subset (the natural themselves) has no sup.
10. p116: the powerset P(S) of S, ordered by ordinary set inclusion, forms a cpo, whose sup is just set union.
11. p116: given any set, adjoining bottom yields a cpo.
12. p117: the set of partial functions between two sets is a cpo. the sup operation is set union.
13. p117: let P be the powerset operator and f : S -> T. P(f) : P(S) -> P(T) is continuous.
14. p117: cpos with continuous functions form a category Cpo.
15. p118: if D, E are cpos, Prod D E is a cpo.
16. p118: if D, E are cpos, the set of continuous functions between D, E forms a cpo.
17. p116: if a poset has a least element, we say it is pointed.
18. p119: fixed point theorem: if D is a pointed cpo and f : D -> D is continuous then it has a fixed point.
19. p119: we can give the semantics of a while loop using fixed points. a while loop is the fixed point of the functional F : (part M M) -> (part M M) given by F(f)(m) := if [[B]]m = false then m else f([[C]]m), where (part M M) is the set of partial functions for memory to memory, [[B]] assigns memory to a boolean value, and [[C]] is a command, understood as a partial function from memory (input) to memory (output). 
