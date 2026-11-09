import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstraction

namespace Flapjack.WordToStackProofs

/-- Successful abstraction retains the number of source frames and consumes
one length entry for each frame, under only the source success premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_IMP_LENGTH"
  (words_as_type_indexed_bitvec)]
theorem absStackImpLength {width : Nat} {frameWidth : Nat} [NeZero width] [NeZero frameWidth]
    (bitmaps : List (BitVec width)) (frames : List (WordSemStackFrame frameWidth))
    (stack : List (WordLocW width)) (lens : List Nat)
    (result : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (h : absStack bitmaps frames stack lens = some result) :
    result.length = frames.length ∧ lens.length = frames.length := by
  revert result
  fun_induction absStack bitmaps frames stack lens
  all_goals simp_all

end Flapjack.WordToStackProofs
