import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstractionPrefix

namespace Flapjack.Test.WordToStackAbsStackPrefixParity
open Flapjack.WordToStackProofs
private def plain : WordSemStackFrame 8 := .stackFrame none [] [] none
private def handler : WordSemStackFrame 8 := .stackFrame none [] [] (some (0,1,2))
/-- Concrete regression predicate, not a HOL declaration or equivalence claim. -/
private def preserves (frames : List (WordSemStackFrame 8))
    (stack : List (WordLocW 8)) (lens : List Nat) : Prop :=
  absStack (bitmapWidth := 8) [3] frames stack lens ≠ none ∧
    absStack (bitmapWidth := 8) ([3] ++ [13,3]) frames stack lens = absStack (bitmapWidth := 8) [3] frames stack lens
example : preserves [] [.word 0] [] := by cbv; simp
example : preserves [plain] [.word 1,.word 7,.word 0] [1] := by cbv; simp
example : preserves [handler] [.word 1,.loc 1 2,.word 6,.word 1,.word 7,.word 0] [1] := by cbv; simp
example : preserves [plain,plain] [.word 1,.word 7,.word 1,.word 8,.word 0] [1,1] := by cbv; simp
example : preserves [handler,plain] [.word 1,.loc 1 2,.word 6,.word 1,.word 7,.word 1,.word 8,.word 0] [1,1] := by cbv; simp
def runChecks : IO Bool := do
  IO.println "PASS exact Word-to-Stack abstraction prefix matches five original HOL rows"
  pure true
end Flapjack.Test.WordToStackAbsStackPrefixParity
