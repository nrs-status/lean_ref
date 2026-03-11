
def explicit_eqrec.{u, v}
  (α : Sort v)
  (a : α)
  (motive : (a_1 : α) -> a = a_1 -> Sort u) -- given a construction schema dependent on a_1, a = a_1
  (refl : motive a (.refl a)) -- supposing this construction schema can be realized with a, a = a
  (a_1 : α)
  (t : a = a_1) -- given a_1, a = a_1
  : motive a_1 t -- this construction schema can be realized with a_1, a = a_1
  := @Eq.rec α a motive refl a_1 t

-- programming in mltt
def eqrec_as_elimrule
  (α : Sort u)
  (a b : α)
  (c : a = b)
  (motive : (x y : α) -> x = y -> Sort v)
  (d : (x : α) -> motive x x (.refl x))
  : motive a b c 
  := Eq.rec (motive := fun a_1 eq => motive a a_1 eq) (d a) c

-- hottbook
def pathind
  (α : Sort u)
  (C : (x y : α) -> x = y -> Sort v)
  (c : (x : α) -> C x x (.refl x))
  : (x y : α) -> (p : x = y) -> C x y p
  := fun _ _ p => explicit_eqrec _ _ _ (c _) _ p

def pathind_computation_rule
  (α : Sort u)
  (C : (x y : α) -> x = y -> Sort v)
  (c : (x : α) -> C x x (.refl x))
  (x : α)
  : pathind α C c x x (.refl x) = c x := rfl


-- hottbook; corresponds to Lean's Eq.rec
def based_pathind
  (α : Sort u)
  (a : α)
  (C : (x : α) -> a = x -> Sort v)
  (c : C a (.refl a))
  : (x : α) -> (p : a = x) -> C x p
  := fun _ p => Eq.rec c p

def based_pathind_computation_rule
  (α : Sort u)
  (a : α)
  (C : (x : α) -> a = x -> Sort v)
  (c : C a (.refl a))
  : based_pathind α a C c a (.refl a) = c := rfl

-- the essence of the computational content of Eq.rec
def Eq.crec
  (α : Sort u)
  (a : α)
  (motive : (a_1 : α) -> a = a_1 -> Sort v)
  (at_refla : motive a (.refl a))
  (a_1 : α)
  (t : a = a_1)
  : motive a_1 t
  := match t with
  | .refl .(a) => at_refla


def Eq.crec'
  (α : Sort u)
  (a : α)
  (motive : (a_1 : α) -> a = a_1 -> Sort v)
  (at_refla : motive a (.refl a))
  (a_1 : α)
  (t : a = a_1)
  : motive a_1 t
  := match a, a_1, t with
  | a, .(a), .refl .(a) => at_refla


def Eq.crec''
  (α : Sort u)
  (a : α)
  (motive : (a_1 : α) -> a = a_1 -> Sort v)
  (at_refla : motive a (.refl a))
  (a_1 : α)
  (t : a = a_1)
  : motive a_1 t
  := explicit_eqrec _ _ _ at_refla _ _

def explicit_eq_casesOn
  (α : Sort u_1)
  (a : α)
  (motive : (a_1 : α) -> a = a_1 -> Sort u)
  (a_1 : α)
  (t : a = a_1)
  (at_refl_a : motive a (.refl a))
  : motive a_1 t 
  := explicit_eqrec _ _ _ at_refl_a _ _


theorem eq_symm {x y : α} : x = y -> y = x :=
  fun eq => 
    -- Eq.rec states: if motive x (.refl x) holds
    -- then given (t : x = y)
    -- motive y t holds
    explicit_eqrec 
      α x 
      (fun a_1 _ => a_1 = x)
      (.refl x)
      y eq 

theorem eq_trans {x y z : α} : x = y -> y = z -> x = z :=
  fun eqa => 
    explicit_eqrec
     α x
     (fun a_1 (_ : x = a_1) => a_1 = z -> x = z)
     id
     y eqa

theorem eq_subst {α} {motive : α -> Prop} {a b : α} 
  (ha : a = b) : motive a -> motive b
  := explicit_eqrec
    _ _
    (fun a_1 (_ : a = a_1) => motive a -> motive a_1)
    id
    _ ha

/-
prior to indexing (unlike Eq.rec)
-/

/-
in ndrec form:
to prove P(x,y)
it suffices to prove P(x,x) and x = y
-/

theorem prior_to_indexing_ndrec
  {α} {motive : α -> α -> Prop} -- can be arbitrary sort
  {a b : α}
  (refl : motive a a)
  (eq : a = b)
  : motive a b
  := Eq.rec (motive := fun a_1 _ => motive a a_1) refl eq
/-
dependently:
to prove P(x,y,eq) where eq : x = y
it suffices to prove P(x,x, .refl x) and x = y
-/

theorem prior_to_indexing_drec
  {α} {motive : (x y : α) -> x = y -> Prop} -- can be arbitrary sort
  {a b : α}
  (refl : motive a a (.refl a))
  (eq : a = b)
  : motive a b eq
  := Eq.rec (motive := fun a_1 eq' => motive a a_1 eq') refl eq


/- 
indexed forms (the form of Eq.rec)
-/

/-
ndrec:
to prove P(y)
it suffices to prove P(x) and x = y
-/

theorem indexed_ndrec
  {α} (a : α)
  {motive : (x : α) -> Prop}
  {b : α}
  (refl : motive a)
  (eq : a = b)
  : motive b
  := Eq.rec (motive := fun a_1 _ => motive a_1) refl eq

/-
ndrec:
to prove P(y,eq) where eq: x = y
it suffices to prove P(x, .refl x) and x = y
-/

theorem indexed_drec
  {α} (a : α)
  {motive : (x : α) -> a = x -> Prop}
  {b : α}
  (refl : motive a (.refl a))
  (eq : a = b)
  : motive b eq
  := Eq.rec (motive := motive) refl eq


def dimot_reduction
  (α : Sort u)
  (dimot : (x y : α) -> Sort v)
  (a : α) : 
  Σ'unimot : (y : α) -> Sort v, 
  (y : α) -> unimot y = dimot a y
  := ⟨fun y' => dimot a y', fun _ => rfl⟩



