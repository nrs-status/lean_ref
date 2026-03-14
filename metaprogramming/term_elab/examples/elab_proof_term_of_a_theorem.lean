import Lean
import Qq

open Qq
open Lean Elab Expr Meta

elab "test" : term => do
  let u : Level := .param `u
  withLocalDeclDQ `α q(Sort u) fun α =>
  withLocalDeclDQ `x q($α) fun x =>
  withLocalDeclDQ `y q($α) fun y => 
  withLocalDeclDQ `eq q($x = $y) fun eq => do
    let myexpr : Expr := q(@Eq.rec $α $x (fun a_1 _ => a_1 = $x) (Eq.refl $x) $y $eq)
    mkLambdaFVars #[α, x, y, eq] myexpr

def mythm' : (α : Sort u) -> (x y : α) -> (eq : x = y) -> y = x := 
  test

