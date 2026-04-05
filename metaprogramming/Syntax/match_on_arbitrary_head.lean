/-- info: match! -/
#guard_msgs in
#eval show Lean.Elab.TermElabM Unit from do
  let stx <- `(Nat.add 5 7)
  match stx with
  | `($(_) 5 7) => dbg_trace "match!"
  | _ => dbg_trace "nomatch!"
