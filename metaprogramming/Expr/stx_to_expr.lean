def myelab : TermElabM Unit := do
  let stx : Syntax <- `(Empty ⊕ Unit ⊕ Empty ⊕ Fin 2)
  let expr : Expr <- do Lean.Elab.Term.elabTerm stx .none
  dbg_trace expr
