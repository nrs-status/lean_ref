Std/Data/DHashMap/Internal/Defs.lean
-  only `Internal.Index`, `Internal.Defs` and `Internal.AssocList.Basic` contain
any executable code. The rest of the files set up the verification framework which is described in
the remainder of this text.
- The basic idea is to translate statements about hash maps into statements about lists using the
function `toListModel` defined in this file. The function `toListModel` simply concatenates all
buckets into a `List ((a : α) × β a)`. The file `Internal.List.Associative` then contains a complete
verification of associative lists. The theorems relating the operations on `Raw₀` to the operations
on `List ((a : α) × β a)` are located in `Internal.WF` and have such names as
`contains_eq_containsKey` or `toListModel_insert`. In the file `Internal.RawLemmas` we then state
all of the lemmas for `Raw₀` and use a tactic to apply the results from `Internal.WF` to reduce to
the results from `Internal.List.Associative`. From there we can state the actual lemmas for
`DHashMap.Raw`, `DHashMap`, `HashMap.Raw`, `HashMap`, `HashSet.Raw` and `HashSet` in the
non-internal `*.Lemmas` files and immediately reduce them to the results about `Raw₀` in
`Internal.RawLemmas`.
