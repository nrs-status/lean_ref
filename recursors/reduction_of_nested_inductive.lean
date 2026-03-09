inductive Mytyp
| unit 
| w_nat (n : Nat)
| recur : Mytyp -> Mytyp -> Mytyp
| recur2 : List Mytyp -> Mytyp


/--
Mytyp.rec.{u} 
  {motive_1 : Mytyp → Sort u} 
  {motive_2 : List Mytyp → Sort u} 
  (unit : motive_1 Mytyp.unit)
  (w_nat : (n : Nat) → motive_1 (Mytyp.w_nat n))
  (recur : 
    (a a_1 : Mytyp) → 
    motive_1 a → 
    motive_1 a_1 → 
    motive_1 (a.recur a_1))
  (recur2 : 
    (a : List Mytyp) → 
    motive_2 a → 
    motive_1 (Mytyp.recur2 a)) 
  (nil : motive_2 [])
  (cons : 
    (head : Mytyp) → 
    (tail : List Mytyp) → 
    motive_1 head → 
    motive_2 tail → 
    motive_2 (head :: tail)) 
    (t : Mytyp) :
  motive_1 t
-/

theorem mytyp_rec_at_unit : @Mytyp.rec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons .unit = at_unit := rfl

theorem mytyp_rec_at_w_nat : @Mytyp.rec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons (.w_nat n) = at_w_nat n := rfl

theorem mytyp_rec_at_recur : @Mytyp.rec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons (.recur x y) = at_recur x y 
  (@Mytyp.rec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons x) 
  (@Mytyp.rec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons y) 
  := rfl

theorem mytyp_rec_at_recur' :
    let myrec := @Mytyp.rec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons
    myrec (.recur x y) = at_recur x y (myrec x) (myrec y)
    := rfl

theorem mytyp_rec_at_recur2 :
    @Mytyp.rec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons (.recur2 l) 
    = 
    at_recur2 l (@Mytyp.rec_1 mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons l)
    := rfl
