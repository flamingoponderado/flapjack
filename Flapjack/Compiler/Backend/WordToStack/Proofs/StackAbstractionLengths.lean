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
  induction frames generalizing stack lens result with
  | nil =>
      cases lens with
      | nil =>
          simp only [absStack] at h
          split at h <;> simp_all
      | cons len lens => simp [absStack] at h
  | cons frame frames ih =>
      cases frame with
      | stackFrame size nonGc gc handler =>
          cases stack with
          | nil => cases lens <;> simp [absStack] at h
          | cons w stack =>
              cases lens with
              | nil => simp [absStack] at h
              | cons len lens =>
                  cases handler with
                  | none =>
                      cases hb : StackSem.fullReadBitmap bitmaps w with
                      | none => simp [absStack, hb] at h
                      | some bits =>
                          simp only [absStack, hb] at h
                          split at h <;> simp_all
                          cases hr : absStack bitmaps frames (stack.drop len) lens with
                          | none => simp [hr] at h
                          | some ys =>
                              have hi := ih _ _ ys hr
                              simp only [hr, Option.some.injEq] at h
                              obtain ⟨_, he⟩ := h
                              subst result
                              simpa using hi
                  | some handler =>
                      cases stack with
                      | nil => simp [absStack] at h
                      | cons loc stack =>
                          cases stack with
                          | nil => simp [absStack] at h
                          | cons hv stack =>
                              cases stack with
                              | nil => simp [absStack] at h
                              | cons bitmap stack =>
                                  cases hb : StackSem.fullReadBitmap bitmaps bitmap with
                                  | none => simp [absStack, hb] at h
                                  | some bits =>
                                      simp only [absStack, hb] at h
                                      split at h <;> simp_all
                                      cases hr : absStack bitmaps frames (stack.drop len) lens with
                                      | none => simp [hr] at h
                                      | some ys =>
                                          have hi := ih _ _ ys hr
                                          simp only [hr, Option.some.injEq] at h
                                          obtain ⟨_, _, he⟩ := h
                                          subst result
                                          simpa using hi

end Flapjack.WordToStackProofs
