
inductive mytyp | a | b | c | d | e | f

def mymatch : mytyp -> Nat :=
  fun xmytyp => match xmytyp with
  | .a => 0
  | .c => 1
  | _ => 2

/--
info: private def mymatch.match_1.splitter.{u_1} : (motive : mytyp → Sort u_1) →
  (xmytyp : mytyp) →
    (Unit → motive mytyp.a) →
      (Unit → motive mytyp.c) →
        ((x : mytyp) → (x = mytyp.a → False) → (x = mytyp.c → False) → motive x) → motive xmytyp :=
fun motive xmytyp h_1 h_2 h_3 => mymatch._sparseCasesOn_1 xmytyp (h_1 ()) (h_2 ()) fun h => h_3 xmytyp ⋯ ⋯
-/
#guard_msgs in
#print mymatch.match_1.splitter

def mymatch' : mytyp -> Nat :=
  fun xmytyp => match xmytyp with
  | .a => 0
  | .c => 1
  | .d => 2
  | .f => 3
  | _ => 4

/--
info: private def mymatch'.match_1.splitter.{u_1} : (motive : mytyp → Sort u_1) →
  (xmytyp : mytyp) →
    (Unit → motive mytyp.a) →
      (Unit → motive mytyp.c) →
        (Unit → motive mytyp.d) →
          (Unit → motive mytyp.f) →
            ((x : mytyp) →
                (x = mytyp.a → False) →
                  (x = mytyp.c → False) → (x = mytyp.d → False) → (x = mytyp.f → False) → motive x) →
              motive xmytyp :=
fun motive xmytyp h_1 h_2 h_3 h_4 h_5 =>
  mymatch'._sparseCasesOn_1 xmytyp (h_1 ()) (h_2 ()) (h_3 ()) (h_4 ()) fun h => h_5 xmytyp ⋯ ⋯ ⋯ ⋯
-/
#guard_msgs in
#print mymatch'.match_1.splitter

