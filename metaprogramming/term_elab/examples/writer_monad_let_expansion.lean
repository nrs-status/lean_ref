import Mathlib.Control.Monad.Writer
import Batteries.Tactic.OpenPrivate
import Qq

open Lean Elab Term Meta PrettyPrinter Syntax
open Qq

inductive LetBindingLHS
| name (n : Name) | prod_ctor (stx : Syntax) | anon_ctor (stx : Syntax)
deriving Repr, Inhabited

inductive LetBindingBinding
| def_ | bind
deriving Repr

structure LetBinding where
  lhs : LetBindingLHS
  binding : LetBindingBinding
  rhs_stx : String
  typeName : String
  rhs_val : Dynamic

deriving instance TypeName for Nat

instance : Repr LetBinding where
  reprPrec := fun lb n =>
    reprPrec lb.binding n ++ reprPrec lb.binding n ++ reprPrec lb.rhs_stx n

abbrev MyWriter := WriterT (Array LetBinding)


syntax (name := let'_stx) "let' " ident (" : " term)? " := " term : doElem


set_option pp.notation false
def mkTellTerm (id_nm : Lean.Name) (rhs_stx : Syntax) : TermElabM Expr := do
  let lhs_ctor : Q(LetBindingLHS) := q(LetBindingLHS.name $id_nm)
  let rhs_str_expr : Q(String) := mkStrLit (<- formatTerm rhs_stx).pretty'
  let lctx <- getLCtx
  let decl := lctx.getFromUserName! id_nm
  let ty_as_str : String := (<- Meta.ppExpr decl.type).pretty'
  let decl_ty_nm : Q(String) := mkStrLit ty_as_str
  let dynval_expr : Q(Dynamic) <- mkAppM ``Dynamic.mk #[decl.value]
  let expr := q(MonadWriter.tell (ω := Array LetBinding) (M := MyWriter IO) #[.mk $lhs_ctor .def_ $rhs_str_expr $decl_ty_nm $dynval_expr])
  .pure expr


@[doElem_elab let'_stx]
def let'_elab : Do.DoElab := 
  fun stx do_cont => 
  match stx with
  | `(doElem|let' $id $[: $ty]? := $body) => do
    let let_stx <- (match ty with
      | .some ty' => `(letDecl|$id : $ty' := $body)
      | .none => `(letDecl|$id := $body))
    let id_as_nm := Lean.TSyntax.getId id
    let nm <- mkFreshUserName `___x
    Do.elabDoLetOrReassign (.let .none) let_stx {
      resultName := nm
      resultType := q(Unit)
      k := do
        let e <- mkTellTerm id_as_nm body
        do_cont.mkBindUnlessPure e
        }
  | _ => throwUnsupportedSyntax

set_option backward.do.legacy false
def myLoggedTest' : MyWriter IO Unit := do
  let' x : Nat := 5
  IO.println "hi"
  let' y : Nat := x + x
  IO.println y

/--
info: hi
10
#[LetBindingBinding.def_LetBindingBinding.def_"5", LetBindingBinding.def_LetBindingBinding.def_"x + x"]
-/
#guard_msgs in
#eval show IO Unit from do
  let r <- myLoggedTest'.run
  dbg_trace repr r.2
  .pure .unit


