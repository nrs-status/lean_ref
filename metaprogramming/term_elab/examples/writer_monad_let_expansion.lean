import Mathlib.Control.Monad.Writer
import Qq

open Lean Elab Term Meta PrettyPrinter Syntax
open Qq

deriving instance Lean.ToExpr for String.Pos.Raw
deriving instance Lean.ToExpr for Substring.Raw
deriving instance Lean.ToExpr for Lean.SourceInfo
deriving instance Lean.ToExpr for Lean.Syntax

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
  typeName : Expr
  rhs_val : Dynamic

deriving instance TypeName for 
  Nat, String, Bool

abbrev MyWriter := WriterT (Array LetBinding)

syntax (name := let'_stx) "let' " ident (" : " term)? " := " term : doElem

def mkTellTerm (id_nm : Lean.Name) (rhs_stx : Syntax) : TermElabM Expr := do
  let lhs_ctor : Q(LetBindingLHS) := q(LetBindingLHS.name $id_nm)
  let rhs_stx_expr : Q(Syntax) := toExpr rhs_stx
  let lctx <- getLCtx
  let decl := lctx.getFromUserName! id_nm
  let typ_stx_expr : Q(Expr) := toExpr decl.type
  let dynval_expr : Q(Dynamic) <- mkAppM ``Dynamic.mk #[decl.value]
  let expr := q(MonadWriter.tell (ω := Array LetBinding) (M := MyWriter IO) #[.mk $lhs_ctor .def_ $rhs_stx_expr $typ_stx_expr $dynval_expr])
  .pure expr


@[doElem_elab let'_stx]
def let'_elab : Do.DoElab := 
  fun stx do_cont => 
  match stx with
  | `(doElem|let' $id $[: $ty]? := $body) => do
    let let_stx <- (match ty with
      | .some ty' => `(letDecl|$id : $ty' := $body)
      | .none => `(letDecl|$id := $body))
    Do.elabDoLetOrReassign (.let .none) let_stx {
      resultName := <- mkFreshUserName `__x
      resultType := q(Unit)
      k := do
        let e <- mkTellTerm (getId id) body
        do_cont.mkBindUnlessPure e
        }
  | _ => throwUnsupportedSyntax

def LetBinding.pp_rhs_stx (lb : LetBinding) : TermElabM String := do
  let rhs_format <- formatTerm lb.rhs_stx
  .pure rhs_format.pretty'

def LetBinding.pp_typeName (lb : LetBinding) : TermElabM String := do
  let typeName_format <- Meta.ppExpr lb.typeName
  .pure typeName_format.pretty'

def LetBinding.pp (lb : LetBinding) : TermElabM String := do
  let lhs_repr := repr lb.lhs
  .pure (lhs_repr.pretty' ++ "\n" ++ (<- lb.pp_rhs_stx) ++ "\n" ++ (<- lb.pp_typeName))

set_option backward.do.legacy false
def myLoggedTest' : MyWriter IO Unit := do
  let' x : Nat := 5
  IO.println "hi"
  let' y : Nat := x + x
  IO.println y

#print myLoggedTest'

#eval show TermElabM Unit from do
  let r <- myLoggedTest'.run
  for lb in r.2 do
    dbg_trace <- lb.pp
    dbg_trace "\n"


