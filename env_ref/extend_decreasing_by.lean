def summands_wf (h : summands a = .some (l, r)) : sizeOf r < sizeOf a := by
  simp [summands] at h; split at h <;> grind
macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply_rules [summands_wf])
