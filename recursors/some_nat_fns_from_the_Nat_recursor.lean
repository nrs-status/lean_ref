
/-
a Nat recursor implementing addition looks like:
0 -> id
1 -> fun m => (.succ ∘ @0) m
2 -> fun m => .succ ∘ @1
...
-/

def recadd := @Nat.rec
  (fun _ => Nat -> Nat)
  id
  (fun _ rec_app_on_subterm =>
    (Nat.succ ∘ rec_app_on_subterm)
    )

def recadd' := @Nat.rec
  (fun _ => Nat -> Nat)
  id
  (fun _ rec_app_on_subterm =>
    (fun m => (Nat.succ ∘ rec_app_on_subterm) m
    ))

/-
a Nat recursor implementing multiplication looks like:
0 -> fun _ => 0
1 -> fun m => m
2 -> fun m => m + @1 m
3 -> fun m => m + @2 m
-/
def recmul := @Nat.rec
  (fun _ => Nat -> Nat)
  (fun _ => 0)
  (fun _ rec_app_on_subterm =>
    fun m => m + rec_app_on_subterm m)
