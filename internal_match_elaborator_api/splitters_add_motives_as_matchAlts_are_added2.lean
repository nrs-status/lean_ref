inductive mytyp | a | b | nat (n : Nat)

def mymatch : mytyp × mytyp -> mytyp :=
  fun xprod => match xprod with
  | ⟨.a, .a⟩ => .nat 0
  | _ => .nat 1

def mymatch' : mytyp × mytyp -> mytyp :=
  fun xprod => match xprod with
  | ⟨.a, _⟩ => .nat 0
  | ⟨.b, _⟩ => .nat 1
  | _ => .nat 2

def mymatch'' : mytyp × mytyp -> mytyp :=
  fun xprod => match xprod with
  | ⟨.a, _⟩ => .nat 0
  | ⟨.nat n, _⟩ => .nat (1 + n)
  | _ => .nat 1

/--
info: private def mymatch.match_1.splitter.{u_1} : (motive : mytyp × mytyp → Sort u_1) →
  (xprod : mytyp × mytyp) →
    (Unit → motive (mytyp.a, mytyp.a)) →
      ((x : mytyp × mytyp) → (x = (mytyp.a, mytyp.a) → False) → motive x) → motive xprod :=
fun motive xprod h_1 h_2 =>
  Prod.casesOn xprod fun fst snd =>
    mymatch._sparseCasesOn_1 fst (mymatch._sparseCasesOn_1 snd (h_1 ()) fun h => h_2 (mytyp.a, snd) ⋯) fun h =>
      h_2 (fst, snd) ⋯
-/
#guard_msgs in
#print mymatch.match_1.splitter

/--
info: private def mymatch'.match_1.splitter.{u_1} : (motive : mytyp × mytyp → Sort u_1) →
  (xprod : mytyp × mytyp) →
    ((snd : mytyp) → motive (mytyp.a, snd)) →
      ((snd : mytyp) → motive (mytyp.b, snd)) →
        ((x : mytyp × mytyp) →
            (∀ (snd : mytyp), x = (mytyp.a, snd) → False) → (∀ (snd : mytyp), x = (mytyp.b, snd) → False) → motive x) →
          motive xprod :=
fun motive xprod h_1 h_2 h_3 =>
  Prod.casesOn xprod fun fst snd => mymatch'._sparseCasesOn_1 fst (h_1 snd) (h_2 snd) fun h => h_3 (fst, snd) ⋯ ⋯
-/
#guard_msgs in
#print mymatch'.match_1.splitter

/--
info: private def mymatch''.match_1.splitter.{u_1} : (motive : mytyp × mytyp → Sort u_1) →
  (xprod : mytyp × mytyp) →
    ((snd : mytyp) → motive (mytyp.a, snd)) →
      ((n : Nat) → (snd : mytyp) → motive (mytyp.nat n, snd)) →
        ((x : mytyp × mytyp) →
            (∀ (snd : mytyp), x = (mytyp.a, snd) → False) →
              (∀ (n : Nat) (snd : mytyp), x = (mytyp.nat n, snd) → False) → motive x) →
          motive xprod :=
fun motive xprod h_1 h_2 h_3 =>
  Prod.casesOn xprod fun fst snd =>
    mymatch''._sparseCasesOn_1 fst (h_1 snd) (fun n => h_2 n snd) fun h => h_3 (fst, snd) ⋯ ⋯
-/
#guard_msgs in
#print mymatch''.match_1.splitter
