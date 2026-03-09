syntax (name := wCtxMod) "#(" term ")" : term
@[macro wCtxMod]
def wCtxModMacro : Macro
| `(#($x)) => `(term|by simp; exact $x) -- the idea is to figure out how to make this suitably extensible
| _ => Macro.throwUnsupported
