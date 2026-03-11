import Lean
import Batteries.Tactic.OpenPrivate
import Qq

open Qq

open Lean Elab Term Command

open private elabMatchAltView withElaboratedLHS elabPatterns from Lean.Elab.Match

def myview : TermElabM TermMatchAltView := do .pure {
  ref := <- `(`x)
  patterns := #[<- `(Nat.succ y), <- `(Nat.zero)]
  lhs := <- `(`y)
  rhs := .mk .missing }

deriving instance Repr for LocalDecl
deriving instance Repr for Meta.Match.Pattern

def mytesting : ExceptT PatternElabException TermElabM Unit := do
  let matchType : Expr := q(Nat -> Nat -> Nat)
  let alt <- myview
  withRef alt.ref do
    let (patternVars, alt) <- collectPatternVars alt
    withPatternVars patternVars fun patternVarDecls =>
      withElaboratedLHS patternVarDecls alt.patterns alt.lhs 2 matchType fun altLHS matchType => 
      dbg_trace matchType
      dbg_trace altLHS.ref
      dbg_trace altLHS.fvarDecls.repr 0
      dbg_trace altLHS.patterns.repr 0
      .pure .unit
      
/--
info: Nat
(Term.quotedName (name "`y"))
[Lean.LocalDecl.cdecl
   0
   (Lean.Name.mkNum `_uniq 5595)
   (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `y.«_@».Macroexpander.garden2 3217485558) "_hygCtx") "_hyg") 2)
   (Lean.Expr.const `Nat [])
   (Lean.BinderInfo.default)
   (Lean.LocalDeclKind.default)]
[Lean.Meta.Match.Pattern.ctor `Nat.succ [] [] [Lean.Meta.Match.Pattern.var (Lean.Name.mkNum `_uniq 5595)],
 Lean.Meta.Match.Pattern.ctor `Nat.zero [] [] []]
-/
#guard_msgs in
#eval show TermElabM Unit from do
  let xexcept <- mytesting
  let _ <- MonadExcept.ofExcept (xexcept.mapError PatternElabException.ex)
