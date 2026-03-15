import Qq

open Qq
open Lean Meta

inductive LetBindingLHS
| name (n : Name) | prod_ctor (stx : Syntax) | anon_ctor (stx : Syntax)
deriving Repr, Inhabited

inductive LetBindingBinding
| def_ | bind
deriving Repr

structure LetBinding where
  lhs : LetBindingLHS
  binding : LetBindingBinding
  rhs_stx : Syntax
  val_typeName : Lean.Name
  rhs_val : Dynamic

def interpretTypeName (nm : Lean.Name) : Type :=
  if nm == `Nat
  then Nat
  else Empty

elab "lb_val " x:term : term => do
  let lbe <- elabTermEnsuringTypeQ x q(LetBinding)
  let typexpr <- whnf q(interpretTypeName ($lbe).val_typeName)
  mkAppOptM ``Dynamic.get?
    #[typexpr, q(($lbe).rhs_val), <- synthInstance (<- mkAppM ``TypeName #[typexpr])]

deriving instance TypeName for Nat

def mylb : LetBinding := .mk (.name `x) .def_ (.atom .none "5") `Nat (.mk 5)

#eval lb_val mylb
