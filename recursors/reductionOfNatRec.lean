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

theorem nat_recOn_at_zero : @Nat.recOn mot .zero at_zero at_succ = at_zero := rfl
theorem nat_recOn_at_succ : @Nat.recOn mot (.succ nn) at_zero at_succ = at_succ nn (@Nat.recOn mot nn at_zero at_succ) := rfl

/--
info: @[reducible] def Nat.casesOn.{u} : {motive : Nat → Sort u} →
  (t : Nat) → motive Nat.zero → ((n : Nat) → motive n.succ) → motive t :=
fun {motive} t zero succ => Nat.rec zero (fun n n_ih => succ n) t
-/
#guard_msgs in
#print Nat.casesOn

theorem nat_casesOn_at_zero : @Nat.casesOn mot .zero at_zero at_succ = at_zero := rfl
theorem nat_casesOn_at_succ : @Nat.casesOn mot (.succ nn) at_zero at_succ = at_succ nn := rfl
