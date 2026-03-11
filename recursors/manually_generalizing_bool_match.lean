-- Bool.rec requires noncomputable attribute
def boolCases (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α := 
    let generalization : (b' : Bool) -> b = b' -> α := 
      -- fun b' => Bool.rec ifFalse ifTrue b'
      fun b' => Bool.casesOn b' ifFalse ifTrue
    generalization b (.refl b)
