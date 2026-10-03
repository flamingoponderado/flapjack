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

end Flapjack
