run_meta do
  let myexpr : Expr := q(mylang.ops (.pair .s .b))
  dbg_trace myexpr
  let reduced <- Lean.Meta.reduce myexpr true false true
  dbg_trace (<- Lean.PrettyPrinter.ppExpr reduced)
  pure Unit.unit
