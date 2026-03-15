import Lean
import Batteries.Tactic.OpenPrivate
import Macroexpander.ParserUtils
import Qq

open private elabMatchAltView withElaboratedLHS from Lean.Elab.Match

open Lean Meta Match Qq
open Lean Elab Term

def elabMatchesTerm_impl (discr_expr : Expr) (pat_stx : Syntax) : ExceptT PatternElabException TermElabM Expr := do
  let patternVars <- getPatternVars pat_stx
  withPatternVars patternVars fun patternVarDecls => do
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

def elabMatchesTerm (discr_expr : Expr) (pat_stx : Syntax) : TermElabM Expr := do
  trace[Elab.match] "elabMatchesTerm"
  trace[Elab.match] "discr_expr: {discr_expr}"
  trace[Elab.match] "pat_stx: {pat_stx}"
  let r <- elabMatchesTerm_impl discr_expr pat_stx
  match r with
  | .ok rr => .pure rr
  | .error rr => throw rr.ex


def elabDoesntMatch (discr_expr : Expr) (pat_stx : Syntax) : TermElabM Expr := do
  let r <- elabMatchesTerm discr_expr pat_stx
  let doesntmatch <- mkAppM `Eq #[r, q(Bool.false)]
  pure doesntmatch

#eval show TermElabM Unit from do
  let r <- elabDoesntMatch q(Nat.succ Nat.zero) (<- `(Nat.succ nn))
  dbg_trace (<- Lean.PrettyPrinter.ppExpr r)

def withDoesntMatchEqs_aux (discr_expr : Expr) (k : Array Expr -> TermElabM α) (pat_stxs' : Array Syntax) (accum : Array Expr) : TermElabM α := do
  trace[Elab.match] "withDoesntMatchEqs_aux"
  trace[Elab.match] "discr_expr: {discr_expr}"
  if q : pat_stxs'.size == 0 then k accum
  else do
    let hyp_nm := mkIdent <| ("dme" ++ toString pat_stxs'.size).toName
    trace[Elab.match] "pat_stxs'.back: {pat_stxs'.back (by grind)}"
    withLocalDeclD hyp_nm.getId (<- elabDoesntMatch discr_expr (pat_stxs'.back (by grind))) fun h => do
      addTermInfo' hyp_nm h (isBinder := true)
      withDoesntMatchEqs_aux discr_expr k pat_stxs'.pop (accum.push h)
termination_by pat_stxs'.size
decreasing_by grind

def withDoesntMatchEqs (discr_expr : Expr) (pat_stxs : Array Syntax) (k : Array Expr -> TermElabM α) : TermElabM α := 
  withDoesntMatchEqs_aux discr_expr k pat_stxs #[]

open private withToClear from Lean.Elab.Match

deriving instance Repr for Discr

def elabMatchAltView' (discrs : Array Discr) (prev_pats : Array Syntax) (alt : TermMatchAltView) (matchType : Expr) (toClear : Array FVarId) : ExceptT PatternElabException TermElabM (AltLHS × Expr) := withRef alt.ref do
    trace[Elab.match] "elabMatchAltView' start, prev_pats: {prev_pats}"
    let (patternVars, alt) ← collectPatternVars alt
    trace[Elab.match] "patternVars: {patternVars}"
    withPatternVars patternVars fun patternVarDecls => do
      withElaboratedLHS patternVarDecls alt.patterns alt.lhs 1 matchType fun altLHS matchType =>
        withEqs discrs altLHS.patterns fun eqs => do
          let .mk e _ := discrs[0]!
          trace[Elab.match] "e from .mk e _ := discrs[0]!: {e}"
          trace[Elab.match] "elabMatchAltView, discrs.size: {discrs.size}"
          for x in (discrs.map (·.expr)) do
            trace[Elab.match] "pprinting discrs elm"
            trace[Elab.match] (<- Lean.PrettyPrinter.ppExpr x)
          withDoesntMatchEqs e prev_pats fun eqs' =>  -- this line is new
            withLocalInstances altLHS.fvarDecls do
              trace[Elab.match] "elabMatchAltView: {matchType}"
              -- connect match-generalized pattern fvars, which are a suffix of `latLHS.fvarDecls`,
              for (fvar, baseId) in altLHS.fvarDecls.toArray.reverse.zip toClear.reverse do
                pushInfoLeaf <| .ofFVarAliasInfo { id := fvar.fvarId, baseId, userName := fvar.userName }
              let matchType ← instantiateMVars matchType
              let matchType' ← if matchType.getAppFn.isMVar then mkFreshTypeMVar else pure matchType
              withToClear toClear matchType' do
                let rhs ← elabTermEnsuringType alt.rhs matchType'
                unless (← fullApproxDefEq <| isDefEq matchType' matchType) do
                  throwError "Type mismatch: Alternative {← mkHasTypeButIsExpectedMsg matchType' matchType}"
                let xs := altLHS.fvarDecls.toArray.map LocalDecl.toExpr ++ eqs ++ eqs'
                let rhs ← if xs.isEmpty then pure <| mkSimpleThunk rhs else mkLambdaFVars xs rhs
                trace[Elab.match] "rhs: {rhs}"
                return (altLHS, rhs)

open private generalize getIndexToInclude? mkFreshDiscrIdentFrom mkUserNameFor from Lean.Elab.Match

-- changed everything up to handlePatternElabException; after that line it's just the normal elab function 

deriving instance Repr for Pattern

partial def elabMatchAltViews' (generalizing? : Option Bool) (toClear : Array FVarId) (discrs : Array Discr) (matchType : Expr) (altViews : Array TermMatchAltView) (prev_pats : Array Syntax) (accum : Array (AltLHS × Expr)) (first? : Option (Term.SavedState × Exception)) := show TermElabM (Array Discr × Expr × Array (AltLHS × Expr) × Bool) from do
  trace[Elab.match] "elabMatchViews'"
  trace[Elab.match] "discrs: {discrs.map (·.expr)}"
  trace[Elab.match] "prev_pats: {prev_pats}"
  let s <- saveState
  let { discrs := discrs', toClear := toClear', matchType := matchType', altViews := altViews', refined } <- generalize discrs matchType altViews generalizing?
  trace[Elab.match] m!"altViews.size {altViews.size}"
  trace[Elab.match] "discrs': {discrs'.map (·.expr)}"
  if p : altViews.size == 0 
  then do
    .pure ⟨discrs', matchType', accum, first?.isSome || refined⟩
  else
    let r <- elabMatchAltView' discrs' prev_pats (altViews.back (by grind)) matchType (toClear ++ toClear')
    match r with
    | .error rr => handlePatternElabException rr s 
    | .ok rr =>
      let first_pat <- Lean.PrettyPrinter.delab (<- rr.1.patterns[0]!.toExpr)
      elabMatchAltViews' generalizing? toClear discrs matchType altViews.pop (prev_pats.push first_pat) (accum.push rr) first?
where
  handlePatternElabException (ex s) := match ex with
    | { patternIdx := patternIdx, pathToIndex := pathToIndex, ex := ex } => do
      let discr := discrs[patternIdx]!
      let some index ← getIndexToInclude? discr.expr pathToIndex
        | throwEx (← updateFirst first? ex)
      trace[Elab.match] "index to include: {index}"
      if (← discrs.anyM fun discr => isDefEq discr.expr index) then
        throwEx (← updateFirst first? ex)
      let first ← updateFirst first? ex
      s.restore (restoreInfo := true)
      let indices ← collectDeps #[index] (discrs.map (·.expr))
      let matchType ← try
        updateMatchType indices matchType
      catch _ => throwEx first
      let ref ← getRef
      trace[Elab.match] "new indices to add as discriminants: {indices}"
      let wildcards ← indices.mapM fun index => do
        if index.isFVar then
          let localDecl ← index.fvarId!.getDecl
          if localDecl.userName.hasMacroScopes then
            return mkHole ref
          else
            let id := mkIdentFrom ref localDecl.userName
            `(?$id)
        else
          return mkHole ref
      let altViews  := altViews.map fun altView => { altView with patterns := wildcards ++ altView.patterns }
      let indDiscrs ← indices.mapM fun i => do
        match discr.h? with
        | none => return { expr := i : Discr }
        | some h =>
          -- If the discriminant that introduced this index is annotated with `h : discr`, then we should annotate the new discriminant too.
          let h ← mkFreshDiscrIdentFrom h
          return { expr := i, h? := h : Discr }
      let discrs    := indDiscrs ++ discrs
      let indexFVarIds := indices.filterMap fun | .fvar fvarId .. => some fvarId | _  => none
      elabMatchAltViews' generalizing? (toClear ++ indexFVarIds) discrs matchType altViews prev_pats accum first
      --discrs (toClear ++ indexFVarIds) matchType altViews first

  throwEx {α} (p : Term.SavedState × Exception) : TermElabM α := do
    p.1.restore (restoreInfo := true); throw p.2

  updateFirst (first? : Option (Term.SavedState × Exception)) (ex : Exception) : TermElabM (Term.SavedState × Exception) := do
    match first? with
    | none       => return (← saveState, ex)
    | some first => return first

  containsFVar (es : Array Expr) (fvarId : FVarId) : Bool :=
    es.any fun e => e.isFVar && e.fvarId! == fvarId

  collectDeps (indices : Array Expr) (discrs : Array Expr) : TermElabM (Array Expr) := do
    let mut s : CollectFVars.State := {}
    for discr in discrs do
      s := collectFVars s (← instantiateMVars (← inferType discr))
    let (indicesFVar, indicesNonFVar) := indices.partition Expr.isFVar
    let indicesFVar := indicesFVar.map Expr.fvarId!
    let mut toAdd := #[]
    for fvarId in s.fvarSet.toList do
      unless containsFVar discrs fvarId || containsFVar indices fvarId do
        let localDecl ← fvarId.getDecl
        for indexFVarId in indicesFVar do
          if (← localDeclDependsOn localDecl indexFVarId) then
            toAdd := toAdd.push fvarId
    let indicesFVar ← sortFVarIds (indicesFVar ++ toAdd)
    return indicesFVar.map mkFVar ++ indicesNonFVar

  updateMatchType (indices : Array Expr) (matchType : Expr) : TermElabM Expr := do
    let matchType ← indices.foldrM (init := matchType) fun index matchType => do
      let indexType ← inferType index
      let matchTypeBody ← kabstract matchType index
      let userName ← mkUserNameFor index
      return Lean.mkForall userName BinderInfo.default indexType matchTypeBody
    check matchType
    return matchType

def elabAtomicDiscr (discr : Syntax) : TermElabM Expr := do
  let term := discr[1]
  trace[Elab.match] "elabAtomicDiscr, discr: {discr}"
  trace[Elab.match] "elabAtomicDiscr, term: {term}"
  trace[Elab.match] "elabAtommicDiscr, discr[0]: {discr[0]}"
  trace[Elab.match] "elabAtomicDiscr, discr: {discr}"
  elabTerm discr none


open private isMatchUnit? from Lean.Elab.Match

partial def elabMatchTypeAndDiscrs (discrStxs : Array Syntax) (matchOptMotive : Syntax) (matchAltViews : Array TermMatchAltView) (expectedType : Expr)
      : TermElabM ElabMatchTypeAndDiscrsResult := do
  if matchOptMotive.isNone then
    elabDiscrs 0 #[]
  else
    -- motive := leading_parser atomic ("(" >> nonReservedSymbol "motive" >> " := ") >> termParser >> ")"
    let matchTypeStx := matchOptMotive[0][3]
    let matchType ← elabType matchTypeStx
    let (discrs, isDep) ← elabDiscrsWithMatchType matchType
    trace[Elab.match] "in fn, discrs: {repr discrs}"
    return { discrs := discrs, matchType := matchType, isDep := isDep, alts := matchAltViews }
where
  /-- Easy case: elaborate discriminant when the match-type has been explicitly provided by the user.  -/
  elabDiscrsWithMatchType (matchType : Expr) : TermElabM (Array Discr × Bool) := do
    let mut discrs := #[]
    let mut i := 0
    let mut matchType := matchType
    let mut isDep := false
    for discrStx in discrStxs do
      i := i + 1
      matchType ← whnf matchType
      match matchType with
      | Expr.forallE _ d b _ =>
        let discr ← fullApproxDefEq <| elabTermEnsuringType discrStx[1] d
        trace[Elab.match] "discr #{i} {discr} : {d}"
        if b.hasLooseBVars then
          isDep := true
        matchType := b.instantiate1 discr
        discrs := discrs.push { expr := discr }
      | _ =>
        throwError "Invalid motive provided to match-expression: Function type with arity {discrStxs.size} expected"
    trace[Elab.match] "in fn, elabDiscrsWithMatchType, discrs: {discrs.map (·.expr)}"
    return (discrs, isDep)

  markIsDep (r : ElabMatchTypeAndDiscrsResult) :=
    { r with isDep := true }

  expandDiscrIdent : Syntax → MetaM Syntax
    | stx@`(_) => mkFreshDiscrIdentFrom stx
    | stx => return stx

  /-- Elaborate discriminants inferring the match-type -/
  elabDiscrs (i : Nat) (discrs : Array Discr) : TermElabM ElabMatchTypeAndDiscrsResult := do
    if h : i < discrStxs.size then
      let discrStx := discrStxs[i]
      trace[Elab.match] "arg for elabAtomicDiscr, discrStx[i]: {discrStx}"
      let discr     ← elabAtomicDiscr discrStx
      trace[Elab.match] "elabAtomicDiscr result: {discr}"
      let discr     ← instantiateMVars discr
      let userName ← mkUserNameFor discr
      let h? ←
        if discrStx[0].isNone then
          pure none
        else
          let h ← expandDiscrIdent discrStx[0][0]
          pure (some h)
      let discrs := discrs.push { expr := discr, h? }
      let mut result ← elabDiscrs (i + 1) discrs
      let matchTypeBody ← kabstract result.matchType discr
      if matchTypeBody.hasLooseBVars then
        result := markIsDep result
      /-
        We use `transform (usedLetOnly := true)` to eliminate unnecessary let-expressions.
        This transformation was added to address issue #1155, and avoid an unnecessary dependency.
        In issue #1155, `discrType` was of the form `let _discr := OfNat.ofNat ... 0 ?m; ...`, and not removing
        the unnecessary `let-expr` was introducing an artificial dependency to `?m`.
        TODO: make sure that even when this kind of artificial dependency occurs we catch it before sending
        the term to the kernel.
      -/
      let discrType ← transform (usedLetOnly := true) (← instantiateMVars (← inferType discr))
      let matchType := Lean.mkForall userName BinderInfo.default discrType matchTypeBody
      return { result with matchType }
    else
      for e in discrs.map (·.expr) do
        trace[Elab.match] "lastret discr: {(<- Lean.PrettyPrinter.ppExpr e)}"
      return { discrs, alts := matchAltViews, isDep := false, matchType := expectedType }

def elabMatchAux' (generalizing? : Option Bool) (discrStxs : Array Syntax) (altViews : Array TermMatchAltView) (matchOptMotive : Syntax) (expectedType : Expr)
    : TermElabM Expr := do
  let mut generalizing? := generalizing?
  if !matchOptMotive.isNone then
    if generalizing? == some true then
      throwError "The '(generalizing := true)' parameter is not supported when the 'match' motive is explicitly provided"
    generalizing? := some false
  let (discrs, matchType, altLHSS, isDep, rhss) ← commitIfDidNotPostpone do
    trace[Elab.match] "pre elabMatchTypeAndDiscrs call, altViews.size: {altViews.size}"
    trace[Elab.match] "pre elabMatchTypeAndDiscrs call, discrStxs: {discrStxs}"
    trace[Elab.match] "pre elabMatchTypeAndDiscrs call, expectedType: {expectedType}"
    trace[Elab.match] "pre elabMatchTypeAndDiscrs call, altViews lhs: {altViews.map (·.patterns)}"
    let ⟨discrs, matchType, isDep, altViews⟩ ← elabMatchTypeAndDiscrs discrStxs matchOptMotive altViews expectedType
    trace[Elab.match] "post elabMatchTypeAndDiscrs call, discrs: {discrs.map (·.expr)}"
    trace[Elab.match] "pre matchAlts from liftMacroM, altViews.size: {altViews.size}"
    let matchAlts ← liftMacroM <| expandMacrosInPatterns altViews
    trace[Elab.match] "matchType: {matchType}"
    trace[Elab.match] "pre elabMatchAltViews' call, matchAlts.size: {matchAlts.size}"
    trace[Elab.match] "pre elabMatchAltViews' call, discrs: {discrs.map (·.expr)}"
    let (discrs, matchType, alts, refined) ← elabMatchAltViews' generalizing? #[] discrs matchType matchAlts #[] #[] .none --only line changed
    let isDep := isDep || refined
    synthesizeSyntheticMVarsUsingDefault
    let rhss := alts.map Prod.snd
    let matchType ← instantiateMVars matchType
    let altLHSS ← instantiateAltLHSs (alts.map Prod.fst)
    trace[Elab.match] "altLHSS length immediate post assignment: {altLHSS.length}"
    trace[Elab.match] "alts size: {alts.size}"
    return (discrs, matchType, altLHSS, isDep, rhss)
  if let some r ← if isDep then pure none else isMatchUnit? altLHSS rhss then
    return r
  else
    let numDiscrs := discrs.size
    let matcherName ← mkAuxName `match
    trace[Elab.match] "matcherName: {matcherName}"
    trace[Elab.match] "pre_mkMatcher matchType: {matchType}"
    trace[Elab.match] "altLHSS length: {altLHSS.length}"
    let matcherResult ← Lean.Elab.Term.mkMatcher { matcherName, matchType, discrInfos := discrs.map fun discr => { hName? := discr.h?.map (·.getId) }, lhss := altLHSS }
    reportMatcherResultErrors altLHSS matcherResult
    matcherResult.addMatcher
    let motive ← forallBoundedTelescope matchType numDiscrs fun xs matchType => mkLambdaFVars xs matchType
    let r := mkApp matcherResult.matcher motive
    let r := mkAppN r (discrs.map (·.expr))
    let r := mkAppN r rhss
    trace[Elab.match] "result: {r}"
    return r

open Lean.Parser

def matchesParser : Parser := leading_parser:leadPrec
  termParser >> " with" >> ppDedent Lean.Parser.Term.matchAlts

syntax (name := match'_with_parser) "match' " matchesParser : term


def getDiscrs' (matchstx : Syntax) : Array Syntax :=
  #[matchstx[1][0]]

def getMatchAlts' (k : SyntaxNodeKinds) : Syntax -> Array (MatchAltView k)
| `(match' $discr with $alts:matchAlt*) => alts.filterMap (getMatchAlt k)
| _ => #[]

#print AltLHS
  open private waitExpectedTypeAndDiscrs getDiscrs getMatchGeneralizing? getMatchOptMotive from Lean.Elab.Match

  def elabMatchCore (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
    let expectedType   ← waitExpectedTypeAndDiscrs stx expectedType?
    trace[Elab.match] m!"expectedType: {expectedType}"
    let discrStxs      := getDiscrs' stx
    let gen?           := getMatchGeneralizing? stx
    trace[Elab.match] m!"gen?: {gen?}"
    let altViews       := getMatchAlts' _ stx
    let matchOptMotive := getMatchOptMotive stx
    elabMatchAux' gen? discrStxs altViews.reverse matchOptMotive expectedType --only line changed


open private expandSimpleMatch expandNonAtomicDiscrs? from Lean.Elab.Match

@[term_elab match'_with_parser]
def elabMatch' : TermElab := fun stx expectedType? => do
  match stx with
  | `(match' $discr:term with | $y:ident => $rhs) =>
     if (← isPatternVar y) then expandSimpleMatch stx discr y rhs expectedType? else elabMatchDefault stx expectedType?
  | _ => elabMatchDefault stx expectedType?
where
  elabMatchDefault (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
    match (← liftMacroM <| expandMatchAlts? stx) with
    | some stxNew => withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
    | none =>
    match (← expandNonAtomicDiscrs? stx) with
    | some stxNew => withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
    | none =>
      let discrs' := getDiscrs' stx
      trace[Elab.match] m!"discrs': {discrs'}"
      let matchOptMotive := getMatchOptMotive stx
      trace[Elab.match] m!"matchOptMotive: {matchOptMotive}"
      if !matchOptMotive.isNone && discrs'.any fun d => !d[0].isNone then
        throwErrorAt matchOptMotive "match motive should not be provided when discriminants with equality proofs are used"
      trace[Elab.matc] m!"stx when calling elabMatchCore: {stx}"
      elabMatchCore stx expectedType?



def test (n : Nat) : Bool := 
  match' n with
  | Nat.zero => Bool.true
  | Nat.succ (Nat.succ Nat.zero) => Bool.true
  | Nat.succ nn => Bool.true






