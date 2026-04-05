1. An expression that starts with `'` and continues with an identifier produces a symbol value.
example:
```
> 'a
'a

> (symbol? 'a)
#t

> (eq? 'a (string->symbol "a"))
#t
```
2. Whitespace or special characters can be included in an identifier by quoting them with | or \. 
```
> (string->symbol "one, two")
'|one, two|

> (string->symbol "6")
'|6|
```
3. Forms like `define`, `lambda`, and `let` bind identifiers. The part of the program for which the binding applies is the scope of the binding. The set of bindings in effect for a given expression is the expression’s environment.
4. An expression `'datum` is a shorthand for `(quote datum)`
5. `unquote` is similar to `quote`. However, for each (unquote expr) that appears within the datum, the expr is evaluated to produce a value that takes the place of the unquote sub-form.
```
(quasiquote (1 2 (unquote (+ 1 2)) (unquote (- 5 1))))
'(1 2 3 4)
```
6. The `unquote-splicing` form is similar to `unquote`, but its expr must produce a list, and the `unquote-splicing` form must appear in a context that produces either a list or a vector.
```
> (quasiquote (1 2 (unquote-splicing (list (+ 1 2) (- 5 1))) 5))
'(1 2 3 4 5)
```
7. Shorthands:
- `quasiquote`: `
- `unquote`: ,
- `unquote-splicing`: ,@
8. Some identifiers correspond to variables, some refer to syntactic forms (such as `lambda`, which is the syntactic form for functions), some refer to transformers for macro expansion, and some are quoted to produce symbols or syntax objects. An identifier binds another (i.e., it is a binding) when the former is parsed as a variable or syntactic form and the latter is parsed as a reference to the former; the latter is bound. For example, as a fragment of source, the text
```
(let ([x 5]) x)
``` 
includes two identifiers: `let` and `x` (which appears twice). When this source is parsed in a context where `let` has its usual meaning, the first `x` binds the second `x`.

9. A form is a fragment of a program, such as an identifier or a function call. A form is represented as a syntax object, and each syntax object has an associated set of scopes (i.e., a scope set). In the above example, the representations of the `x`s include the scope that corresponds to the `let` form.
10. When a form parses as the binding of a particular identifier, parsing updates a global table that maps a combination of an identifier’s symbol and scope set to its meaning: a variable, a syntactic form, or a transformer. An identifier refers to a particular binding when the reference’s symbol and the identifier’s symbol are the same, and when the reference’s scope set is a superset of the binding’s scope set. For a given identifier, multiple bindings may have scope sets that are subsets of the identifier’s; in that case, the identifier refers to the binding whose set is a superset of all others; if no such binding exists, the reference is ambiguous (and triggers a syntax error if it is parsed as an expression). A binding shadows any binding (i.e., it is shadowing any binding) with the same symbol but a subset of scopes.
11. A syntax object combines a simpler Racket value, such as a symbol or pair, with lexical information, source-location information, syntax properties, and whether the syntax object is tainted. The lexical information of a syntax object comprises a set of scope sets, one for each phase level. In particular, an identifier is represented as a syntax object containing a symbol, and its lexical information can be combined with the global table of bindings to determine its binding (if any) at each phase level.
12.
```
(syntax-rules (literal-id ...)
  [(id . pattern) template] ...)
``` 
is equivalent to
```
(lambda (stx)
  (syntax-case stx (literal-id ...)
    [(generated-id . pattern) (syntax-protect #'template)]  ...))
```
13. Syntax for the `syntax-case` form:
```
(syntax-case stx-expr (literal-id ...)
  clause ...)
```
Unlike syntax-rules, the syntax-case form does not produce a procedure. Instead, it starts with a stx-expr expression that determines the syntax object to match against the patterns.
```
> (syntax->datum
   (syntax-case #'(+ 1 2) ()
    [(op n1 n2) #'(- n1 n2)]))
'(- 1 2)
```
14. Expanding a use of a macro creates a new scope in the same way that a binding form creates a new scope.
