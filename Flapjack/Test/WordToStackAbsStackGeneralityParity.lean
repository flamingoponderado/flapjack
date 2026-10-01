import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstractionPrefix
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstractionLengths

/-! Original HOL observations with genuinely distinct saved-frame and
bitmap/target-stack word dimensions. Saved locals and predicted frame sizes
are deliberately different from target words: the source ignores them here. -/
namespace Flapjack.Test.WordToStackAbsStackGeneralityParity
open Flapjack.WordToStackProofs

private def plain16 : WordSemStackFrame 16 :=
  .stackFrame (some 999) [(7, .word 65535)] [(9, .loc 40 41)] none
private def handler16 : WordSemStackFrame 16 :=
  .stackFrame (some 999) [(7, .word 65535)] [(9, .loc 40 41)] (some (999,42,43))
private def plain1 : WordSemStackFrame 1 :=
  .stackFrame (some 999) [(7, .word 1)] [(9, .loc 40 41)] none
private def handler1 : WordSemStackFrame 1 :=
  .stackFrame (some 999) [(7, .word 1)] [(9, .loc 40 41)] (some (999,42,43))

example : absStack (width := 8) (frameWidth := 16) [3] [] [.word 0] [] = some [] := by cbv
example : absStack (width := 8) (frameWidth := 1) [3] [] [.word 0] [] = some [] := by cbv
example : absStack (width := 8) [3] [plain16] [.word 1,.word 7,.word 0] [1] =
    some [(none,[true],[.word 7])] := by cbv
example : absStack (width := 8) [3] [handler16]
    [.word 1,.loc 1 2,.word 6,.word 1,.word 7,.word 0] [1] =
    some [(some (.loc 1 2,.word 6),[true],[.word 7])] := by cbv
example : absStack (width := 8) [3] [plain1] [.word 1,.word 7,.word 0] [1] =
    some [(none,[true],[.word 7])] := by cbv
example : absStack (width := 8) [3] [handler1]
    [.word 1,.loc 1 2,.word 6,.word 1,.word 7,.word 0] [1] =
    some [(some (.loc 1 2,.word 6),[true],[.word 7])] := by cbv
example : absStack (width := 8) [3] [handler16,plain16]
    [.word 1,.loc 1 2,.word 6,.word 1,.word 7,.word 1,.word 8,.word 0] [1,1] =
    some [(some (.loc 1 2,.word 6),[true],[.word 7]),(none,[true],[.word 8])] := by cbv
example : absStack (width := 8) [3] [handler16] [.word 2] [1] = none := by cbv

example {width frameWidth : Nat} [NeZero width] [NeZero frameWidth]
    (bitmaps more : List (BitVec width)) (frames : List (WordSemStackFrame frameWidth))
    (stack : List (WordLocW width)) (lens : List Nat)
    (result : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (h : absStack bitmaps frames stack lens = some result) :
    absStack (bitmaps ++ more) frames stack lens = some result ∧
      (result.length = frames.length ∧ lens.length = frames.length) :=
  ⟨absStackBitmapsPrefix bitmaps frames stack lens more result h,
    absStackImpLength bitmaps frames stack lens result h⟩

end Flapjack.Test.WordToStackAbsStackGeneralityParity
