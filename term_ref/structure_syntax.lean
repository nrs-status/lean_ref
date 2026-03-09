{env, options := {}}

def categoryParser (catName : Name) (prec : Nat) : Parser where
  fn := adaptCacheableContextFn ({ · with prec }) (withCacheFn catName (categoryParserFn catName))
