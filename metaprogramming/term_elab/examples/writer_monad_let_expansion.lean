import Mathlib.Control.Monad.Writer
import Qq

open Lean Elab Term Meta Syntax
open Qq

inductive LetBindingLHS
| name (n : Name) | prod_ctor (stx : Syntax) | anon_ctor (stx : Syntax)
deriving Repr

structure LetBinding where
  lhs : LetBindingLHS
  rhs : String
  typeName : Lean.Name
  rhs_val : Dynamic

deriving instance TypeName for Nat

instance : Repr LetBinding where
  reprPrec := fun lb n =>
    reprPrec lb.lhs n ++ " " ++ reprPrec lb.rhs n ++ " " ++ reprPrec lb.typeName n

def myMonad : IO Unit := do
  let x := 5
  IO.println x
  let x' := x + x
  IO.println x'

abbrev MyWriter := WriterT (Array LetBinding)

def myNewMonad : MyWriter IO Unit := do
  let x : Nat := 5
  tell #[.mk (.name `x) "5" `Nat (.mk x)]
  IO.println x
  let x' := x + x
  tell #[.mk (.name `x') "x + x" `Nat (.mk x')]
  IO.println x'


syntax (name := let'_stx) "let' " ident (" : " term)? " := " term : doElem

set_option pp.notation false
@[doElem_elab let'_stx]
def let'_elab : Do.DoElab := 
  fun stx do_cont => 
  match stx with
  | `(doElem|let' $id $[: $ty]? := $body) => do
    let let_stx <- (match ty with
      | .some ty' => `(letDecl|$id : $ty' := $body)
      | .none => `(letDecl|$id := $body))
    let id_as_nm := Lean.TSyntax.getId id
    let nm_stx : TSyntax `term := mkStrLit id_as_nm.toString
    let nm_ctor_stx <- `(term|LetBindingLHS.name (Name.mkSimple $nm_stx))
    let nm <- mkFreshUserName `___x
    Do.elabDoLetOrReassign (.let .none) let_stx {
      resultName := nm
      resultType := q(Unit)
      k := do
        let lctx <- getLCtx
        let declx := lctx.getFromUserName! id_as_nm
        let expr <- mkAppOptM ``MonadWriter.tell 
          #[.none, q(MyWriter IO), .none, <- mkAppM ``Array.mkArray1 #[<- mkAppM ``LetBinding.mk #[
            (<- elabTerm nm_ctor_stx (.some q(LetBindingLHS))),
            Lean.mkStrLit (<- PrettyPrinter.ppExpr declx.value).pretty',
            <- mkAppM ``Name.mkSimple #[Lean.mkStrLit (<- PrettyPrinter.ppExpr declx.type).pretty'],
            (<- mkAppM ``Dynamic.mk #[declx.value])
          ]]]
        do_cont.mkBindUnlessPure expr
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
#[LetBindingLHS.name `x "5" `Nat, LetBindingLHS.name `y "HAdd.hAdd x x" `Nat]
-/
#guard_msgs in
#eval show IO Unit from do
  let r <- myLoggedTest'.run
  dbg_trace repr r.2
  .pure .unit
