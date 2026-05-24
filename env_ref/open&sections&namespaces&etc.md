- scoped notation example
```
namespace NS
scoped notation "{!{" e "}!}" => (e, e)
def three := 3
end NS

open scoped NS
def x := {!{ "pear" }!}
```
- to close `open` commands, enclose it into a `section`
```
section

open blah

...
end
```
- you can use `#where` to print information about the current scope, i.e., information about the `namespace`, `open`, `variable`, `universe`, and `set_option` commands
