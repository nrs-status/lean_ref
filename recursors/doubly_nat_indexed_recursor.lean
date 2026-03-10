def double_nat_recursor.{u} 
  (motive : Nat -> Nat -> Sort u)
  (initial_construction : motive .zero .zero)
  (leftwise_construction : (n m : Nat) -> motive n m -> motive n.succ m)
  (rightwise_construction : (n m : Nat) -> motive n m -> motive n m.succ)
  (n m : Nat)
  : motive n m := match n, m with
  | .zero, .zero => initial_construction
  | .succ nn, m => 
    leftwise_construction nn m (double_nat_recursor motive initial_construction leftwise_construction rightwise_construction nn m)
  | n, .succ mm => 
    rightwise_construction n mm (double_nat_recursor motive initial_construction leftwise_construction rightwise_construction n mm)

def double_nat_recursor_add := double_nat_recursor
  (fun _ _ => Nat)
  .zero
  (fun _nn _m motnm => 
    --suppose motnm is the construction parallel to the path traced by nn and m
    --show the construction parallel to the movement motive nn m -> motive nn.succ m
    motnm.succ)
  (fun _n _mm motnm => 
    --suppose motnm is the construction parallel to the path traced by n and mm
    --show the construction parallel to the movement motive n mm -> motive n mm.succ
    motnm.succ)
