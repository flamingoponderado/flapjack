import Flapjack.Compiler.Backend.WordToStack.Proofs.Frames
namespace Flapjack.Test.WordToStackFramesParity
open Flapjack.WordToStackProofs
example : handlerVal (width := 8) [] = 1 := by cbv
example : handlerVal (width := 8) [(none, [true,false], [.word 0, .loc 1 2])] = 4 := by cbv
example : handlerVal (width := 8) [(some (.loc 1 2, .word 0), [], [.word 0])] = 6 := by cbv
example : isHandlerFrame (width := 8) (.stackFrame none [] [] none) = false := by cbv
example : isHandlerFrame (width := 8) (.stackFrame none [] [] (some (0,1,2))) = true := by cbv
example : sortedEnv (width := 8) (.stackFrame none [] [] none) = true := by cbv
example : sortedEnv (width := 8) (.stackFrame none [] [(6,.word 0),(4,.word 0),(2,.word 0)] none) = true := by cbv
example : sortedEnv (width := 8) (.stackFrame none [] [(2,.word 0),(2,.word 0)] none) = false := by cbv
example : sortedEnv (width := 8) (.stackFrame none [] [(2,.word 0),(4,.word 0)] none) = false := by cbv

def runChecks : IO Bool := do
  IO.println "PASS exact Word-to-Stack frame predicates match nine original HOL rows"
  pure true
end Flapjack.Test.WordToStackFramesParity
