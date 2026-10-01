import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstraction
/-! Kernel replay of all eleven fresh original abstraction branch equations. -/
namespace Flapjack.Test.WordToStackAbsStackParity
open Flapjack.WordToStackProofs
private def plain : List (WordSemStackFrame 8) := [.stackFrame none [] [] none]
private def handler : List (WordSemStackFrame 8) := [.stackFrame none [] [] (some (0,1,2))]
example : absStack (width := 8) (frameWidth := 8) [3] [] [.word 0] [] = some [] := by cbv
example : absStack (width := 8) (frameWidth := 8) [3] [] [] [] = none := by cbv
example : absStack (width := 8) [3] plain [.word 1,.word 7,.word 0] [1] = some [(none,[true],[.word 7])] := by cbv
example : absStack (width := 8) [3] plain [.word 0,.word 0] [1] = none := by cbv
example : absStack (width := 8) [3] plain [.word 1,.word 7,.word 0] [2] = none := by cbv
example : absStack (width := 8) [3] plain [.word 1] [1] = none := by cbv
example : absStack (width := 8) [3] plain [.word 1,.word 7] [1] = none := by cbv
example : absStack (width := 8) [3] handler [.word 1,.loc 1 2,.word 6,.word 1,.word 7,.word 0] [1] =
    some [(some (.loc 1 2,.word 6),[true],[.word 7])] := by cbv
example : absStack (width := 8) [3] handler [.word 2] [1] = none := by cbv
example : absStack (width := 8) [3] handler [.word 1,.loc 1 2] [1] = none := by cbv
example : absStack (width := 8) [3] plain [.word 1] [] = none := by cbv

def runChecks : IO Bool := do
  IO.println "PASS exact Word-to-Stack abstraction matches eleven original HOL equations"
  pure true
end Flapjack.Test.WordToStackAbsStackParity
