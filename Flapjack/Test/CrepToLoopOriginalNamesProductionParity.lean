import Flapjack.Pancake.CrepToLoop.ProductionCompileProg

namespace Flapjack.Test.CrepToLoopOriginalNamesProductionParity
open Flapjack CrepToLoopProduction

private def functions : List (CompiledFunction (BitVec 8)) :=
  [⟨"f", [], .call none "g" [.const 7], .one⟩,
   ⟨"g", [0], .return [.var 0], .one⟩]

/-- Match every row, parameter, body constructor, operand and Call field of
the complete two-function original EVAL result; no label rebasing is accepted. -/
private def fullProgramMatches : List (Nat × List Nat × HolLoopProg 8) → Bool
  | [(64, [], .mark (.seq (.mark (.assign 1 (.const value)))
       (.mark (.seq (.mark (.call none (some 65) [1] none)) (.mark .skip))))),
     (65, [0], .mark (.seq (.mark (.assign 1 (.var 0)))
       (.mark (.seq (.mark (.return [1])) (.mark .skip)))))] => value == 7
  | _ => false

def originalProgramCheck : Bool :=
  match compileProgFromProduction? functions with
  | none => false
  | some output => fullProgramMatches output

private def nameBoundaryCheck : Bool :=
  namesSupported ([⟨"ÿ", [], .skip, .one⟩] : List (CompiledFunction (BitVec 8))) &&
  (compileProgFromProduction? ([⟨"λ", [], .skip, .one⟩] : List (CompiledFunction (BitVec 8)))).isNone &&
  (compileProgFromProduction? ([⟨"f", [], .call none "λ" [], .one⟩] : List (CompiledFunction (BitVec 8)))).isNone &&
  (compileProgFromProduction? ([⟨"f", [], .extCall "λ" 0 0 0 0, .one⟩] : List (CompiledFunction (BitVec 8)))).isNone

example : namesSupported functions = true := by decide +kernel
#guard originalProgramCheck
#guard nameBoundaryCheck

def runChecks : IO Bool := do
  if !originalProgramCheck then throw (IO.userError "complete original Crep-to-Loop rows differ")
  if !nameBoundaryCheck then throw (IO.userError "Crep-to-Loop source name boundary differs")
  IO.println "PASS original-label whole Crep-to-Loop producer: complete two-function original program, Call65/rows64+65, parameters/bodies; explicit top/nested name rejection"

  return true

end Flapjack.Test.CrepToLoopOriginalNamesProductionParity
