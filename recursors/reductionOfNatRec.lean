/-
Nat.rec.{u} 
  {motive : Nat → Sort u} 
  (at_zero : motive Nat.zero) 
  (at_succ : (n : Nat) → motive n → motive n.succ) 
  (t : Nat) :
  motive t
-/

theorem nat_rec_at_zero : @Nat.rec mot at_zero at_succ .zero = at_zero := rfl
theorem nat_rec_at_succ : @Nat.rec mot at_zero at_succ (Nat.succ nn) = at_succ nn (@Nat.rec mot at_zero at_succ nn) := rfl

