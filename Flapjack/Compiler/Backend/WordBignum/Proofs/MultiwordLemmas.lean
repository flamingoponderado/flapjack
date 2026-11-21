module

public import Flapjack.Misc.Multiword
public import Flapjack.Misc.Multiword.Mc.Basics
public import Flapjack.Misc.Multiword.Digits

@[expose] public section

/-! The multiword facts of `cakeml/compiler/backend/proofs/word_bignumProofScript.sml`
that speak about the tagged `n2mw`/`i2mw` encodings. -/

namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack

/-- Flapjack-only helper: the little-endian encoding of a natural number is
empty exactly at zero. It states HOL's `n2mw` clause split once, so the tagged
`i2mw_NOT_NIL` below does not need to unfold the recursive definition. -/
theorem n2mw_ne_nil {width : Nat} [NeZero width] (n : Nat) :
    Misc.Multiword.n2mw (width := width) n ≠ [] ↔ n ≠ 0 := by
  unfold Misc.Multiword.n2mw
  split
  · rename_i h
    simp [h]
  · rename_i h
    exact ⟨fun _ => h, fun _ => by simp⟩

/-- HOL `i2mw_NOT_NIL` (`word_bignumProofScript.sml:2268`): the magnitude word
list of `i2mw` is empty exactly when the integer is zero. HOL's empty list is
annotated at the word list type, as in the source (`[] : α word list`). -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "i2mw_NOT_NIL"
  (words_as_type_indexed_bitvec)]
theorem i2mw_snd_ne_nil {width : Nat} [NeZero width] (i : Int) :
    (Misc.Multiword.i2mw i).2 ≠ ([] : List (BitVec width)) ↔ i ≠ 0 := by
  unfold Misc.Multiword.i2mw
  simp only [n2mw_ne_nil]
  omega

section McLemmas

open Flapjack.Misc.Multiword

/-- HOL `true_pres` (`word_bignumProofScript.sml:1872`): the preconditions of
the listed non-looping machine-code-style functions always hold. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "true_pres"
  (words_as_type_indexed_bitvec)]
theorem true_pres {width : Nat} [NeZero width]
    (r0 r1 r2 r3 r4 r6 r7 r8 r9 r10 r11 : BitVec width) (xs ys : List (BitVec width)) :
    mcSingleMulPre (r0, r1, r2) ∧ mcMulBySingle2Pre (r6, r7, r8) ∧
      mcCmp3Pre (r1, r2, r3, r9, r10, r11) ∧ mcCmpMul2Pre (r6, r7, r8, r9, r10, r11) ∧
      mcCmp2Pre (r0, r2, r10, r11) ∧ mcAdjCmpPre (r0, r3, r8) ∧
      mcIdivModHeaderPre (r6, r11) ∧ mcIadd1Pre (r1, r2, xs, ys) ∧
      mcIadd2Pre (r1, r2, r3, r4, xs, ys) ∧ mcIadd3Pre (r1, xs, ys) ∧
      mcIsubFlipPre (r1, r2) ∧ mcImul1Pre (r10, r11) ∧ mcSub1Pre r6 ∧
      mcCmp2Pre (r0, r2, r10, r11) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [mcSingleMulPre_def, mcMulBySingle2Pre_def, mcCmp3Pre_def, mcCmpMul2Pre_def,
      mcCmp2Pre_def, mcAdjCmpPre_def, mcIdivModHeaderPre_def, mcIadd1Pre_def, mcIadd2Pre_def,
      mcIadd3Pre_def, mcIsubFlipPre_def, mcImul1Pre_def, mcSub1Pre_def]

/-- HOL `single_add_word_imp_0_1` (`word_bignumProofScript.sml:1895`): the
carry word of `single_add_word` is zero or one. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "single_add_word_imp_0_1"
  (words_as_type_indexed_bitvec)]
theorem single_add_word_imp_0_1 {width : Nat} [NeZero width] (x1 x2 x3 y1 y2 : BitVec width) :
    singleAddWord x1 x2 x3 = (y1, y2) → y2 ≠ 0 → y2 = 1 := by
  intro h hne
  simp only [singleAddWord, singleAdd] at h
  cases h
  revert hne
  generalize decide (2 ^ width ≤ _) = c
  cases c <;> simp [b2w, b2n]

/-- HOL `mw_ok_SND_i2mw` (`word_bignumProofScript.sml:2275`): the magnitude
digits of `i2mw` are well formed. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "mw_ok_SND_i2mw"
  (words_as_type_indexed_bitvec)]
theorem mw_ok_SND_i2mw {width : Nat} [NeZero width] (fg : Int) :
    Misc.Multiword.mwOk (Misc.Multiword.i2mw fg : Bool × List (BitVec width)).2 := by
  simp only [Misc.Multiword.i2mw]
  exact Misc.Multiword.mwOk_n2mw _

end McLemmas

end Flapjack.Compiler.Backend.WordBignum
