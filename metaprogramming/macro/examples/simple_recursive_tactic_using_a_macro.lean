syntax "custom_tactic" : tactic
macro_rules
| `(tactic| custom_tactic) => `(tactic| apply And.intro <;> custom_tactic)
