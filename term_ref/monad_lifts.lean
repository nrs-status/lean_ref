-- recall you can find instances with the batteries #instances command, see commands/find_instances.lean

#eval show TermElabM Unit from do
  let r <- liftMacroM <| expandMatchAlts? (<- my_match_stx)
  dbg_trace r

