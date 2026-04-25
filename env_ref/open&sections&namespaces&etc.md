- scoped notation example
```
namespace NS
scoped notation "{!{" e "}!}" => (e, e)
def three := 3
end NS

open scoped NS
def x := {!{ "pear" }!}
```
