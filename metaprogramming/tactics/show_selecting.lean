def summands (e : Expr) : Option (Expr × Expr) :=
  match e with
  | .app (.app _ leftsummand) rightsummand => .some (leftsummand, rightsummand)
  | _ => .none

def summands_wf (h : summands a = .some (l, r)) : sizeOf r < sizeOf a := by
  simp [summands] at h; split at h <;> grind
macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply_rules [summands_wf])

def genSumInjs (injectedVal injectedValType : Expr) : Expr -> MetaM (Option Expr) :=
  fun e =>
  match h : summands e with
  | .some (leftsummand, rightsummand) => do
    if (<- isDefEq injectedValType leftsummand)
    then .pure <| mkAppN (.const ``Sum.inl [0,0]) #[leftsummand, rightsummand, injectedVal]
    else if (<- isDefEq injectedValType rightsummand)
      then .pure <| mkAppN (.const ``Sum.inr [0,0]) #[leftsummand, rightsummand, injectedVal]
      else match (<- genSumInjs injectedVal injectedValType rightsummand) with
      | .none => .pure .none
      | .some x => .pure <| mkAppN (.const ``Sum.inr [0,0]) #[leftsummand, rightsummand, x]
  | _ => .pure .none

def getGoalExpr : TacticM Expr := do
  let goal <- getMainGoal
  let goalDecl <- goal.getDecl
  .pure goalDecl.type

def show_selecting_tacticm (injValTyp injVal : Expr) : TacticM Unit := do
  match (<- genSumInjs injVal injValTyp (<- getGoalExpr)) with
  | .some x => closeMainGoal "show_selecting".toName x
  | .none => throwError "genSumInjs failure"

syntax (name := show_selecting_parser) "show_selecting " term " from " term : term

@[term_elab show_selecting_parser]
def show_selecting_termelab : TermElab := fun stx xopte => do
  let .some expectedType := xopte | throwError "no expected type"
  let `(term|show_selecting $injValTyp:term from $injVal:term) := stx | throwUnsupportedSyntax
  let ty <- elabType injValTyp
  let goal <- mkFreshExprSyntheticOpaqueMVar expectedType
  let tac_ctx : Tactic.Context := { elaborator := decl_name% }
  let tac_state : Tactic.State := { goals := [goal.mvarId!] }
  let val <- (Lean.Elab.Tactic.elabTerm injVal ty).run tac_ctx |>.run' tac_state -- borrowing Tactic's elabTerm because otherwise proofs in the term don't elaborate
  let runnable_tac := show_selecting_tacticm ty val
  let runnable_tac_thunked_wrt_ctx := ReaderT.run runnable_tac tac_ctx
  let runnable_tac_thunked_wrt_state := StateRefT'.run' runnable_tac_thunked_wrt_ctx tac_state
  runnable_tac_thunked_wrt_state
  instantiateMVars goal


def mytest_raw : Empty ⊕ Unit ⊕ Empty ⊕ Fin 2 := Sum.inr (Sum.inl Unit.unit)
def mytest : Empty ⊕ Unit ⊕ Empty ⊕ Fin 2 := show_selecting Unit from Unit.unit

def mytest'_raw : Empty ⊕ Unit ⊕ Empty ⊕ Fin 2 := Sum.inr (Sum.inr (Sum.inr (Fin.mk 1 (by simp))))
def mytest' : Empty ⊕ Unit ⊕ Empty ⊕ Fin 2 := show_selecting Fin 2 from Fin.mk 1 <| by simp
