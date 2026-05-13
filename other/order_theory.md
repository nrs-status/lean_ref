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
19. p120: we can give the semantics of a while loop using fixed points. a while loop is the fixed point of the functional F : (part M M) -> (part M M) given by F(f)(m) := if [[B]]m = false then m else f([[C]]m), where (part M M) is the set of partial functions for memory to memory, [[B]] assigns memory to a boolean value, and [[C]] is a command, understood as a partial function from memory (input) to memory (output).
20. p120: the factorial function can be given a denotation in the following manner: let F: (part N N) -> (part N N) := fun f n => if n = 0 then 1 else n * f(n-1). Notice that F is not recursive. Since we can prove F is continuous, the fixed point theorem gives us that F has a least fixed point, and the solution will satisfy the following equation: fun n => if n = 0 then 1 else n * recur (n - 1).
21. p123: why do we take the least fixed point? because it yields a _canonical_ solution. p124: a fixed-point operator F is a collection of continuous functions F_D: D^D -> D such that, forall cpo D, forall continuous f : D -> D, F_D(f) = f(F_D(f)). def: a fixed point operator F is uniform := for any pair of continuous functions f : D -> D and g : E -> E, and for any strict continuous function h : D -> E, s.t. the following square commutes <img width="475" height="321" alt="image" src="https://github.com/user-attachments/assets/f223f8ea-2d2d-44d3-ac89-43adf2c9bae3" />, we have h(F_D(f)) = F_E(g). theorem: the least fixed point operator is the unique uniform fixed-point operator.
22. p106: transition rule for application in PCF: (\x : t. M)N -> [x |-> N]M. transition rule for the fixed point operator in PCF : μx : t. M -> [x |-> μx : t. M]M.
23. p128: fixed point semantics for PCF. [[Nat]] := Nat + Bot. [[Bool]] := Bool. [[s -> t]] := cpo of continuous functions from [[s]] to [[t]]. An H-environment ρ is a partial function that assigns to each variable x in H a value ρ(x) in [[H(x)]]. [[H |> M : t]] := a function that assigns to each H-environment ρ a value in [[t]]. i.e. [[H |> M : t]]ρ is in [[t]]. application: [[H |> M(N) : t]]ρ := ([[H |> M : s -> t]]ρ)([[H |> N : s]]ρ).
24. p129: [[H |> μx : t. M : t]]ρ = leastFixedPoint(fun d => [[H, x : t |> M : t]]ρ[x |-> d]) 
