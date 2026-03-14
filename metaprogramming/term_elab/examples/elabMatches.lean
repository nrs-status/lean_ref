import Lean
import Batteries.Tactic.OpenPrivate
import Qq

open private elabMatchAltView withElaboratedLHS from Lean.Elab.Match

open Lean Meta Match Qq
open Lean Elab Term

def elabMatchesTerm_impl (discr_stx pat_stx : Syntax) : ExceptT PatternElabException TermElabM Expr := do
  let patternVars <- getPatternVars pat_stx
  withPatternVars patternVars fun patternVarDecls => do
    let discr_expr <- Lean.Elab.Term.elabTerm discr_stx .none
    let discr_typ <- inferType discr_expr
    let matchType <- mkArrow discr_typ q(Bool)
    withElaboratedLHS patternVarDecls #[pat_stx] pat_stx 1 matchType fun alt _ => do
    let matchType <- mkArrow discr_typ q(Bool)
    let matcher <- Lean.Meta.Match.mkMatcher {
      matcherName := <- mkAuxDeclName `match
      matchType := matchType
      discrInfos := #[{}]
      lhss := [
        alt,
        <- withLocalDeclD `x discr_typ fun x => return {
          ref := <- getRef
          fvarDecls := [<- x.fvarId!.getDecl]
          patterns := [.var x.fvarId!]
        }
      ]
    }
    matcher.addMatcher
    let motive <- withLocalDeclD `_ discr_typ fun _x =>
      mkLambdaFVars #[_x] q(Bool)
    let fvarDecls := alt.fvarDecls.toArray
    let alt1 <- if fvarDecls.isEmpty
      then withLocalDeclD `_ q(Unit) fun _x =>
        mkLambdaFVars #[_x] q(Bool.true)
      else 
        let xs := alt.fvarDecls.toArray.map (·.toExpr)
        mkLambdaFVars xs q(Bool.true)
    let alt2 <- withLocalDeclD `_ discr_typ fun _x =>
      mkLambdaFVars #[_x] q(Bool.false)
    .pure <| mkAppN matcher.matcher #[motive, discr_expr, alt1, alt2]

def elabMatchesTerm (discr_stx pat_stx : Syntax) : TermElabM Expr := do
  let r <- elabMatchesTerm_impl discr_stx pat_stx
  match r with
  | .ok rr => .pure rr
  | .error rr => throw rr.ex

