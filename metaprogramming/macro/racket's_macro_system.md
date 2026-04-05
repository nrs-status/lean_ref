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
8. Some identifiers correspond to variables, some refer to syntactic forms (such as `lambda`, which is the syntactic form for functions), some refer to transformers for macro expansion, and some are quoted to produce symbols or syntax objects. An identifier binds another (i.e., it is a binding) when the former is parsed as a variable or syntactic form and the latter is parsed as a reference to the former; the latter is bound.
8.1. For example, as a fragment of source, the text
```
(let ([x 5]) x)
```
includes two identifiers: `let` and `x` (which appears twice). When this source is parsed in a context where `let` has its usual meaning, the first `x` binds the second `x`.
