https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html#backtracking

def tryM (x : MetaM Unit) : MetaM Unit := do
  let s ← saveState
  try
    x
  catch _ =>
    restoreState s
