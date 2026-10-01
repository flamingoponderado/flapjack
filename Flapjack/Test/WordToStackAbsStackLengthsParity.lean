import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstractionLengths

namespace Flapjack.Test.WordToStackAbsStackLengthsParity
open Flapjack.WordToStackProofs
private def plain : WordSemStackFrame 8 := .stackFrame none [] [] none
private def handler : WordSemStackFrame 8 := .stackFrame none [] [] (some (0,1,2))
/-- Concrete regression predicate, not a HOL declaration or equivalence claim. -/
private def lengths (frames : List (WordSemStackFrame 8))
    (stack : List (WordLocW 8)) (lens : List Nat) : Prop :=
  (absStack [3] frames stack lens).map List.length = some frames.length ∧
    lens.length = frames.length
example : lengths [] [.word 0] [] := by cbv
example : lengths [plain] [.word 1,.word 7,.word 0] [1] := by cbv
example : lengths [handler] [.word 1,.loc 1 2,.word 6,.word 1,.word 7,.word 0] [1] := by cbv
example : lengths [plain,plain] [.word 1,.word 7,.word 1,.word 8,.word 0] [1,1] := by cbv
example : lengths [handler,plain] [.word 1,.loc 1 2,.word 6,.word 1,.word 7,.word 1,.word 8,.word 0] [1,1] := by cbv
def runChecks : IO Bool := do
  IO.println "PASS exact Word-to-Stack abstraction lengths match five original HOL rows"
  pure true
end Flapjack.Test.WordToStackAbsStackLengthsParity
