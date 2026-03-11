/-
good explanation at:
https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/match.3A.20generalizing.2C.20motive.2C.20etc/near/407102671
-/

-- cannot use h in holes because the types of ifTrue and ifFalse have been refined
def boolCases (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α := match h : b with
    | .true => ifTrue _
    | .false => ifFalse _

-- avoids refining the types of ifTrue and ifFalse
def boolCases' (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α := match (generalizing := false) h : b with
    | .true => ifTrue h
    | .false => ifFalse h

-- what boolCases looks like under the hood
def boolCases'' (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α := match (generalizing := false) h : b, ifTrue, ifFalse with
    | .true, iftrue, _ => iftrue _
    | .false, _, iffalse => iffalse _

    | .false, ift, iff => ifFalse _
