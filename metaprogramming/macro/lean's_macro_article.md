1.  In general, we will present hygienic identifiers in the following as n.msc1.msc2.. . ..mscn{tsc1,. . .,tscn} where n is the original name, msc are macro scopes, and tsc top-level scopes, eliding the braces if there are no top-level scopes
as in the example above. We use the dot notation to suggest both the ordered nature of macro scopes and their eventual implementation in Section 4.
2. When a binding core form is encountered, the local context is extended with the bound symbol(s); existing top-level scopes on bindings are discarded at this step since they are only meaningful on references.
3. We will formally define a symbol as an identifier together with a list of macro scopes.
4. When a reference (another core form), i.e. an identifier not in binding position, is encountered, it is resolved according to the following rules:
    1. If the local context has an entry for the same symbol, the reference binds to the corresponding local binding; any top-level scopes are again discarded.
    2. Otherwise, if the identifier is annotated with one or more top-level scopes or matches one or more symbols in the global context, it binds to all of these (to be disambiguated by the elaborator).
    3. Otherwise, the identifier is unbound and an error is generated.
5. We claim that a macro should in fact be interpreted as an effectful computation since two expansions of the same identifier-introducing macro should not return the same syntax tree to avoid unhygienic interactions between them. Thus, as a side effect, it should apply a fresh macro scope to each newly introduced identifier. In particular, a syntax quotation should not merely be seen as a datum, but as an effectful value that obtains and applies this fresh scope to all the identifiers captured by it to immediately ensure hygiene for pattern-based macros.
6. Identifiers carry macro scopes inline in their Name while top-level scopes are held in a separate list.
