import Flapjack.Byte.GetSetByte
import Flapjack.Misc.Alignment
import Flapjack.Misc.GoodDimindex

/-! Original 32/64-bit byte read-after-write laws from `cakeml/misc/miscScript.sml`
(4319-4411): reading back the written byte, and reading a different byte of
the same aligned word. Only the HOL word dimension translates to a
positive-width BitVec; `good_dimindex` is the reviewed `goodDimindex`. -/
namespace Flapjack
open Flapjack.HolByte

@[hol "cakeml/misc/miscScript.sml" "good_dimindex_get_byte_set_byte"
  (words_as_type_indexed_bitvec)]
theorem goodDimindex_getByte_setByte {width : Nat} [NeZero width] (a : BitVec width)
    (b : BitVec 8) (w : BitVec width) (be : Bool) :
    goodDimindex width → getByte a (setByte a b w be) be = b := by
  intro h
  exact getByte_setByte a b w be (by rcases h with rfl | rfl <;> decide)

/-- `byte_align` at a good dimension divides by the bytes-per-word count;
Flapjack infrastructure (HOL unfolds `byte_align_def` and `align_w2n`). -/
theorem holByteAlign_toNat {width : Nat} [NeZero width] (h : goodDimindex width)
    (a : BitVec width) :
    (holByteAlign a).toNat = a.toNat / (width / 8) * (width / 8) := by
  have hp : 2 ^ holLOG2 (width / 8) = width / 8 := by
    rcases h with rfl | rfl
    · rw [holLOG2_eq_log2 (by decide)]; decide
    · rw [holLOG2_eq_log2 (by decide)]; decide
  rw [holByteAlign, holAlign_eq_div, hp, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) a.isLt

/-- One byte of a word is the corresponding slice of its bits; Flapjack
infrastructure for the original FCP reasoning. -/
theorem getLsbD_getByte {width : Nat} [NeZero width] (a w : BitVec width) (be : Bool)
    (i : Nat) (hi : i < 8) :
    (getByte a w be).getLsbD i = w.getLsbD (byteIndex a be + i) := by
  simp [getByte, hi, BitVec.getLsbD_ushiftRight]

/-- Distinct addresses within one aligned word have distinct byte indices,
eight bits apart; Flapjack infrastructure for the `byte_index` disequality step
of the original proof. -/
theorem byteIndex_disjoint {width : Nat} [NeZero width] (h : goodDimindex width)
    (a a' : BitVec width) (be : Bool) (hne : a ≠ a')
    (hal : holByteAlign a = holByteAlign a') :
    byteIndex a be + 8 ≤ byteIndex a' be ∨ byteIndex a' be + 8 ≤ byteIndex a be := by
  have hd : 0 < width / 8 := by rcases h with rfl | rfl <;> decide
  have hq : a.toNat / (width / 8) = a'.toNat / (width / 8) := by
    have := congrArg BitVec.toNat hal
    rw [holByteAlign_toNat h, holByteAlign_toNat h] at this
    exact Nat.eq_of_mul_eq_mul_right hd this
  have hm : a.toNat % (width / 8) ≠ a'.toNat % (width / 8) := by
    intro hm
    apply hne
    apply BitVec.eq_of_toNat_eq
    rw [← Nat.div_add_mod a.toNat (width / 8), ← Nat.div_add_mod a'.toNat (width / 8), hq, hm]
  have h1 := Nat.mod_lt a.toNat hd
  have h2 := Nat.mod_lt a'.toNat hd
  dsimp only [byteIndex]
  split <;> omega

@[hol "cakeml/misc/miscScript.sml" "get_byte_set_byte_diff"
  (words_as_type_indexed_bitvec)]
theorem getByte_setByte_diff {width : Nat} [NeZero width] (a a' : BitVec width)
    (b : BitVec 8) (w : BitVec width) (be : Bool) :
    goodDimindex width ∧ a ≠ a' ∧ holByteAlign a = holByteAlign a' →
      getByte a (setByte a' b w be) be = getByte a w be := by
  rintro ⟨h, hne, hal⟩
  have h8 : 8 ≤ width := by rcases h with rfl | rfl <;> decide
  have hle := byteIndex_add_le h8 a be
  have hdis := byteIndex_disjoint h a a' be hne hal
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_getByte _ _ _ _ hi, getLsbD_getByte _ _ _ _ hi,
    getLsbD_setByte _ _ _ _ _ (by omega)]
  rcases hdis with hd | hd
  · simp [show ¬ byteIndex a' be ≤ byteIndex a be + i by omega,
      show byteIndex a be + i < byteIndex a' be by omega]
  · simp [show byteIndex a' be + 8 ≤ byteIndex a be + i by omega,
      BitVec.getLsbD_of_ge b (byteIndex a be + i - byteIndex a' be) (by omega)]

end Flapjack
