import Lean
import Batteries.Tactic.OpenPrivate
import Qq

open Qq

open Lean Elab Term Command Meta

open private elabMatchAltView withElaboratedLHS elabPatterns withToClear from Lean.Elab.Match

def myview : TermElabM TermMatchAltView := do .pure {
  ref := <- `(`x)
  patterns := #[<- `(Nat.succ y), <- `(Nat.succ nn)]
  lhs := <- `(`y)
  rhs := <- `(y) }

deriving instance Repr for LocalDecl
deriving instance Repr for Meta.Match.Pattern

def elabMatchAltView (discrs : Array Discr) (alt : TermMatchAltView) (matchType : Expr) (toClear : Array FVarId) : ExceptT PatternElabException TermElabM (Lean.Meta.Match.AltLHS × Expr) := withRef alt.ref do
    let (patternVars, alt) ← collectPatternVars alt
    trace[Elab.match] "patternVars: {patternVars}"
    withPatternVars patternVars fun patternVarDecls => do
      withElaboratedLHS patternVarDecls alt.patterns alt.lhs discrs.size matchType fun altLHS matchType =>
        withEqs discrs altLHS.patterns fun eqs =>
          withLocalInstances altLHS.fvarDecls do
            trace[Elab.match] "elabMatchAltView: {matchType}"
            for (fvar, baseId) in altLHS.fvarDecls.toArray.reverse.zip toClear.reverse do
              pushInfoLeaf <| .ofFVarAliasInfo { id := fvar.fvarId, baseId, userName := fvar.userName }
            let matchType ← instantiateMVars matchType
            let matchType' ← if matchType.getAppFn.isMVar then mkFreshTypeMVar else pure matchType
            withToClear toClear matchType' do
              let rhs ← elabTermEnsuringType alt.rhs matchType'
              unless (← fullApproxDefEq <| isDefEq matchType' matchType) do
                throwError "Type mismatch: Alternative {← mkHasTypeButIsExpectedMsg matchType' matchType}"
              let xs := altLHS.fvarDecls.toArray.map LocalDecl.toExpr ++ eqs
              let rhs ← if xs.isEmpty then pure <| mkSimpleThunk rhs else mkLambdaFVars xs rhs
              logInfo m!"rhs: {rhs}"
              return (altLHS, rhs)

def discrs : Array Discr :=
  #[.mk q(Nat.succ Nat.zero) .none, .mk q(Nat.zero) .none]

#check Exception
def myelab : TermElabM Unit := do
  let x <- _root_.elabMatchAltView discrs (<- myview) q(Nat -> Nat -> Nat) #[]
  match x with
  | .error e => logInfo m!"{e.ex.toMessageData}"
  | .ok pair => .pure .unit

/-- info: rhs: fun y nn => y -/
#guard_msgs in
#eval myelab
