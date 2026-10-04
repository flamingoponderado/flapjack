import Flapjack.Misc.Bit

/-!
# HOL `alignment` and `words` `word_slice`

Counterparts of the pinned `HOL/src/n-bit/alignmentScript.sml` (`align`, `aligned`,
`byte_align`, `byte_aligned`) and of `word_slice_def` from `HOL/src/n-bit/wordsScript.sml`.
HOL `'a word` is `BitVec width` (`words_as_type_indexed_bitvec`), `w ' i` is `w.getLsbD i`,
`^HB` is `width - 1`, and an `FCP i. P i` word is `holFcpWord P`, whose bit `i < width` is
`P i`. `byte_align` uses the specified `LOG2` (`holLOG2`), so at widths below 8 it depends on
the unconstrained `LOG2 0`, exactly as in HOL.
-/

namespace Flapjack

/-- The `FCP i. P i` word whose bit `i` is `P i` for `i < width` (Flapjack infrastructure for
HOL's `fcp$FCP` binder at the word carrier `bool ** 'a`). -/
def holFcpWord {width : Nat} (P : Nat → Bool) : BitVec width :=
  (BitVec.ofBoolListLE ((List.range width).map P)).cast (by simp)

theorem getLsbD_holFcpWord {width : Nat} (P : Nat → Bool) (i : Nat) :
    (holFcpWord (width := width) P).getLsbD i = (decide (i < width) && P i) := by
  unfold holFcpWord
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  by_cases hi : i < width
  · simp [hi, List.getD_eq_getElem?_getD]
  · simp [hi, List.getD_eq_getElem?_getD]

/-- Exact HOL `word_slice_def` (`wordsScript.sml:238-241`):
`word_slice h l = λw. FCP i. l ≤ i ∧ i ≤ MIN h ^HB ∧ w ' i`. -/
@[hol "HOL/src/n-bit/wordsScript.sml" "word_slice_def" (words_as_type_indexed_bitvec)]
def holWordSlice {width : Nat} [NeZero width] (h l : Nat) (w : BitVec width) : BitVec width :=
  holFcpWord (fun i => decide (l ≤ i ∧ i ≤ min h (width - 1)) && w.getLsbD i)

/-- Exact HOL `align_def` (`alignmentScript.sml:18`): `align p w = (dimindex (:'a) - 1 '' p) w`. -/
@[hol "HOL/src/n-bit/alignmentScript.sml" "align_def" (words_as_type_indexed_bitvec)]
def holAlign {width : Nat} [NeZero width] (p : Nat) (w : BitVec width) : BitVec width :=
  holWordSlice (width - 1) p w

/-- Exact HOL `aligned_def` (`alignmentScript.sml:20`): `aligned p w = (align p w = w)`. -/
@[hol "HOL/src/n-bit/alignmentScript.sml" "aligned_def" (words_as_type_indexed_bitvec)]
def holAligned {width : Nat} [NeZero width] (p : Nat) (w : BitVec width) : Bool :=
  decide (holAlign p w = w)

/-- Exact HOL `byte_align_def` (`alignmentScript.sml:23-25`):
`byte_align w = align (LOG2 (dimindex (:'a) DIV 8)) w`. -/
@[hol "HOL/src/n-bit/alignmentScript.sml" "byte_align_def" (words_as_type_indexed_bitvec)]
noncomputable def holByteAlign {width : Nat} [NeZero width] (w : BitVec width) : BitVec width :=
  holAlign (holLOG2 (width / 8)) w

/-- Exact HOL `byte_aligned_def` (`alignmentScript.sml:27-29`):
`byte_aligned w = aligned (LOG2 (dimindex (:'a) DIV 8)) w`. -/
@[hol "HOL/src/n-bit/alignmentScript.sml" "byte_aligned_def" (words_as_type_indexed_bitvec)]
noncomputable def holByteAligned {width : Nat} [NeZero width] (w : BitVec width) : Bool :=
  holAligned (holLOG2 (width / 8)) w

/-- `align p` clears the low `p` bits (Flapjack infrastructure). -/
theorem holAlign_eq_shift {width : Nat} [NeZero width] (p : Nat) (w : BitVec width) :
    holAlign p w = (w >>> p) <<< p := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [holAlign, holWordSlice, getLsbD_holFcpWord, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  by_cases hp : p ≤ i
  · have : p + (i - p) = i := by omega
    simp [hp, this, show i ≤ width - 1 by omega, show ¬ i < p by omega]
  · simp [hp, show i < p by omega]

/-- `align p w` as a division (Flapjack infrastructure). -/
theorem holAlign_eq_div {width : Nat} [NeZero width] (p : Nat) (w : BitVec width) :
    holAlign p w = BitVec.ofNat width ((w.toNat / 2 ^ p) * 2 ^ p) := by
  rw [holAlign_eq_shift]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

/-- `aligned p w` holds exactly when `2 ^ p` divides `w2n w`, for every `p`
(Flapjack infrastructure, HOL's `aligned_w2n`/`aligned_ge_dim` combined). -/
theorem holAligned_iff {width : Nat} [NeZero width] (p : Nat) (w : BitVec width) :
    holAligned p w = true ↔ w.toNat % 2 ^ p = 0 := by
  simp only [holAligned, decide_eq_true_eq, holAlign_eq_div]
  have hle : w.toNat / 2 ^ p * 2 ^ p ≤ w.toNat := Nat.div_mul_le_self _ _
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle w.isLt)] at ht
    rw [← ht, Nat.mul_mod_left]
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle w.isLt)]
    exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)

/-- Full original `aligned_add_sub` (`alignmentScript.sml:182-196`): adding or
subtracting an aligned word preserves alignment, for every `p`. -/
@[hol "HOL/src/n-bit/alignmentScript.sml" "aligned_add_sub" (words_as_type_indexed_bitvec)]
theorem alignedAddSub {width : Nat} [NeZero width] :
    ∀ (p : Nat) (a b : BitVec width), holAligned p b = true →
      holAligned p (a + b) = holAligned p a ∧ holAligned p (a - b) = holAligned p a := by
  intro p a b hb
  rw [holAligned_iff] at hb
  by_cases hp : p ≤ width
  · have hd : 2 ^ p ∣ 2 ^ width := Nat.pow_dvd_pow 2 hp
    have hbd : 2 ^ p ∣ b.toNat := Nat.dvd_of_mod_eq_zero hb
    have hsub : 2 ^ p ∣ 2 ^ width - b.toNat := Nat.dvd_sub hd hbd
    constructor <;> apply Bool.eq_iff_iff.mpr <;>
      rw [holAligned_iff, holAligned_iff]
    · rw [BitVec.toNat_add, Nat.mod_mod_of_dvd _ hd, Nat.add_mod, hb, Nat.add_zero, Nat.mod_mod]
    · rw [BitVec.toNat_sub, Nat.mod_mod_of_dvd _ hd, Nat.add_mod,
        Nat.mod_eq_zero_of_dvd hsub, Nat.zero_add, Nat.mod_mod]
  · have hle : 2 ^ width ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)
    have hbz : b.toNat = 0 := by
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt hle)] at hb
      exact hb
    have hb0 : b = 0 := BitVec.eq_of_toNat_eq (by simpa using hbz)
    subst hb0
    simp

end Flapjack
