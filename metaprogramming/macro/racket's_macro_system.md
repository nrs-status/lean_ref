An expression that starts with `'` and continues with an identifier produces a symbol value.
example:
```
> 'a
'a

> (symbol? 'a)
#t

> (eq? 'a (string->symbol "a"))
#t
```
Whitespace or special characters can be included in an identifier by quoting them with | or \. 
```
> (string->symbol "one, two")
'|one, two|

> (string->symbol "6")
'|6|
```
