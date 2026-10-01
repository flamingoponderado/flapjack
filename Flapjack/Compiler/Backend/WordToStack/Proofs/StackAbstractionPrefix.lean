import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstraction
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapAppend

namespace Flapjack.WordToStackProofs

/-- Appending bitmap storage preserves an already successful abstraction.
The source success premise discharges all bounds and recursive decoding. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_bitmaps_prefix"
  (words_as_type_indexed_bitvec)]
theorem absStackBitmapsPrefix {bitmapWidth : Nat} {width : Nat} [NeZero bitmapWidth] [NeZero width]
    (bitmaps : List (BitVec bitmapWidth)) (frames : List (WordSemStackFrame width))
    (stack : List (WordLocW width)) (lens : List Nat)
    (moreBitmaps : List (BitVec bitmapWidth))
    (result : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (h : absStack bitmaps frames stack lens = some result) :
    absStack (bitmaps ++ moreBitmaps) frames stack lens = some result := by
  induction frames generalizing stack lens result with
  | nil =>
      cases lens with
      | nil => simpa [absStack] using h
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
                          have ha := fullReadBitmapAppend bitmaps w bits moreBitmaps hb
                          simp only [absStack, hb, ha] at h ⊢
                          split at h <;> simp_all
                          cases hr : absStack bitmaps frames (stack.drop len) lens <;> simp_all
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
                                      have ha := fullReadBitmapAppend bitmaps bitmap bits moreBitmaps hb
                                      simp only [absStack, hb, ha] at h ⊢
                                      split at h <;> simp_all
                                      cases hr : absStack bitmaps frames (stack.drop len) lens <;> simp_all

end Flapjack.WordToStackProofs
