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
  typeName : Lean.Name
  rhs_val : Dynamic

deriving instance TypeName for Nat

instance : Repr LetBinding where
  reprPrec := fun lb n =>
    reprPrec lb.binding n ++ reprPrec lb.binding n ++ reprPrec lb.rhs_stx n
abbrev MyWriter := WriterT (Array LetBinding)


syntax (name := let'_stx) "let' " ident (" : " term)? " := " term : doElem

def mkTellStx (id : Ident) (typ : Expr) (body : TSyntax `term) : Do.DoElabM (TSyntax `doElem) := do
      let id_namelit <- `(Name.mkSimple $(quote id.getId.toString))
      let typ_stx <- `(String.toName $(quote (<- Meta.ppExpr typ).pretty'))
      let body_as_str <- `($(quote (Std.Format.pretty' (<- formatTerm body))))
      let tell_stx <- `(doElem|MonadWriter.tell 
        (ω := Array LetBinding) 
        (M := MyWriter IO)
        #[LetBinding.mk (LetBindingLHS.name $id_namelit) .def_ $body_as_str ($typ_stx) (Dynamic.mk $id)])
      .pure tell_stx

set_option pp.notation false
@[doElem_elab let'_stx]
def let'_elab' : Do.DoElab := 
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
        let newdecl := (<- getLCtx).getFromUserName! id_as_nm
        let tell_stx <- mkTellStx id newdecl.type body
        Do.elabDoExpr tell_stx do_cont
        }
  | _ => throwUnsupportedSyntax


set_option backward.do.legacy false
def myLoggedTest'' : MyWriter IO Unit := do
  let' x : Nat := 5
  IO.println "hi"
  let' y : Nat := x + x

#print myLoggedTest''

#eval! show IO Unit from do
  let r <- myLoggedTest''.run
  dbg_trace repr r.2
  .pure .unit

