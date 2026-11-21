module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Add

@[expose] public section

/-! Supporting lemmas of the data-to-word subtraction assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Immediate encodings subtract as their integers when the difference is small. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "small_int_Smallnum_sub"
  (words_as_type_indexed_bitvec)]
theorem smallInt_smallnum_sub {width : Nat} [NeZero width] (i1 i2 : Int) :
    goodDimindex width ∧ smallInt width (i1 - i2) →
    (smallnum i1 : BitVec width) - smallnum i2 = smallnum (i1 - i2) := by
  intro _
  rw [smallnum_i2w, smallnum_i2w, smallnum_i2w, Int.mul_sub, Int.sub_eq_add_neg, BitVec.ofInt_add,
    BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-- Signed values of small immediate encodings subtract without overflow. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "small_int_w2i_Smallnum_sub"
  (words_as_type_indexed_bitvec)]
theorem smallInt_toInt_smallnum_sub {width : Nat} [NeZero width] (i1 i2 : Int) :
    goodDimindex width ∧ smallInt width (i1 - i2) ∧ smallInt width i1 ∧ smallInt width i2 →
    ((smallnum i1 : BitVec width) - smallnum i2).toInt =
      (smallnum i1 : BitVec width).toInt - (smallnum i2 : BitVec width).toInt := by
  rintro ⟨good, diff, small1, small2⟩
  have pos : 0 < width := NeZero.pos width
  rw [smallInt_smallnum_sub i1 i2 ⟨good, diff⟩]
  have b := smallnum_signedBounds good _ diff
  have b1 := smallnum_signedBounds good _ small1
  have b2 := smallnum_signedBounds good _ small2
  rw [smallnum_i2w, smallnum_i2w, smallnum_i2w,
    BitVec.toInt_ofInt_eq_self pos b.1 b.2, BitVec.toInt_ofInt_eq_self pos b1.1 b1.2,
    BitVec.toInt_ofInt_eq_self pos b2.1 b2.2]
  ring

/-- Subtracting two words with clear low bits leaves the low bit clear. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_bit_0_sub_lemma"
  (words_as_type_indexed_bitvec)]
theorem wordBit0_sub_lemma {width : Nat} [NeZero width] :
    ∀ w1 w2 : BitVec width, ¬ w1.getLsbD 0 = true ∧ ¬ w2.getLsbD 0 = true →
      ¬ (w1 + -1 * w2).getLsbD 0 = true := by
  rintro w1 w2 ⟨h1, h2⟩
  have dvd : 2 ∣ 2 ^ width := dvd_pow_self 2 (NeZero.ne width)
  have lt := Nat.one_le_two_pow (n := width)
  simp only [BitVec.getLsbD, Nat.testBit_zero, decide_eq_true_eq, BitVec.toNat_add,
    BitVec.toNat_mul, BitVec.toNat_neg] at h1 h2 ⊢
  have even2 : w2.toNat % 2 = 0 := by omega
  rw [Nat.mod_mod_of_dvd _ dvd, Nat.add_mod, Nat.mod_mod_of_dvd _ dvd, Nat.mul_mod _ w2.toNat 2,
    even2]
  simp only [Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
  exact h1

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
