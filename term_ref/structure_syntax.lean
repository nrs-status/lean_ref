{env, options := {}}

for (fvar, baseId) in altLHS.fvarDecls.toArray.reverse.zip toClear.reverse do
  pushInfoLeaf <| .ofFVarAliasInfo { id := fvar.fvarId, baseId, userName := fvar.userName }

def categoryParser (catName : Name) (prec : Nat) : Parser where
  fn := adaptCacheableContextFn ({ · with prec }) (withCacheFn catName (categoryParserFn catName))
