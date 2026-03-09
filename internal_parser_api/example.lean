import Lean.Parser
import Lean.Elab

open Lean Parser Term
open Lean Elab Util

def runParserWithEmptyInit (parserfn : ParserFn) (input : String) : CoreM (Array Syntax) := do
  let env ← mkEmptyEnvironment
  let parseResult := parserfn.run (mkInputContext input "<input>")
    {env, options := {}} (getTokenTable env) (mkParserState input)
  return parseResult.stxStack.toSubarray.array

def includeTokenAux (tk : Token) (p : ParserFn) : ParserFn :=
  adaptUncacheableContextFn 
    (fun ctx => { ctx with tokens := ctx.tokens.insert tk tk}) 
    p

def includeToken (tk : Token) (p : Parser) : Parser :=
  .mk (mkAtomicInfo <| "including" ++ tk) (includeTokenAux tk p.fn)

def matchesParser : Parser := leading_parser:leadPrec
  "if " >> includeToken "matches" termParser >> " matches" >> ppDedent matchAlts

def myparse := runParserWithEmptyInit matchesParser.fn "if Bool.true matches | myzero.thing => blah | anotherthin.thing => yeah"
