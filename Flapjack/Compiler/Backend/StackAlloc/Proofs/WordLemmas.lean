import Flapjack.HolRef
import Flapjack.Misc.GoodDimindex
import Flapjack.Misc.ListEl
import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.Compiler.Backend.WordGcFunctions
import Flapjack.Compiler.Backend.Semantics.StackSem.WordBitmap

/-!
# `stack_allocProof` word and bit lemmas

The evaluator-independent word, bit-length and list lemmas of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` used by
`comp_correct`.  HOL `bit_length` is `Flapjack.StackSem.bitLength`, `w ' i` is
`BitVec.getLsbD`, `GENLIST f n` is `(List.range n).map f`, `word_msb` is
`BitVec.msb`, `(n -- 0) w` is `gcWordBitsLow n w`, `EL` is `holEl` and `LUPDATE`
is `List.set`.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSem Flapjack.Compiler.Backend.WordGcFunctions

/-- Exact HOL `lsl_lsr` (`stack_allocProofScript.sml:28-49`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "lsl_lsr"
  (words_as_type_indexed_bitvec)]
theorem lsl_lsr {width : Nat} [NeZero width] {n : BitVec width} {a : Nat} :
    n.toNat * 2 ^ a < 2 ^ width → (n <<< a) >>> a = n := by
  intro h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos a)]

/-- Exact HOL `bytes_in_word_word_shift` (`stack_allocProofScript.sml:51-62`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "bytes_in_word_word_shift"
  (words_as_type_indexed_bitvec)]
theorem bytesInWord_wordShift {width : Nat} [NeZero width] {n : BitVec width} :
    goodDimindex width ∧ (wordSemBytesInWord : BitVec width).toNat * n.toNat < 2 ^ width →
      (wordSemBytesInWord * n) >>> wordShiftAmount width = n := by
  rintro ⟨hg, hlt⟩
  rw [bytesInWord_mul_eq_shift n hg]
  apply lsl_lsr
  rcases hg with rfl | rfl
  · simpa [wordSemBytesInWord, wordShiftAmount, Nat.mul_comm] using hlt
  · simpa [wordSemBytesInWord, wordShiftAmount, Nat.mul_comm] using hlt

/-- Exact HOL `get_bits_def` (`stack_allocProofScript.sml:150-152`):
`get_bits w = GENLIST (\i. w ' i) (bit_length w − 1)`. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "get_bits_def"
  (words_as_type_indexed_bitvec)]
def getBits {width : Nat} [NeZero width] (w : BitVec width) : List Bool :=
  (List.range (bitLength w - 1)).map w.getLsbD

theorem bitLength_eq {width : Nat} [NeZero width] (w : BitVec width) :
    bitLength w = if w = 0 then 0 else bitLength (w >>> (1 : Nat)) + 1 := by
  rw [bitLength]

theorem ushiftRight_eq_zero_iff {width : Nat} (w : BitVec width) (n : Nat) :
    w >>> n = 0 ↔ w.toNat < 2 ^ n := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos n)).1 this
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos n)).2 h

/-- `bit_length` is the least `n` with `w < 2 ^ n` (Flapjack infrastructure for the
tagged `bit_length` lemmas below). -/
theorem bitLength_spec {width : Nat} [NeZero width] :
    ∀ w : BitVec width, w.toNat < 2 ^ bitLength w ∧
      ∀ n, n < bitLength w → 2 ^ n ≤ w.toNat := by
  intro w
  induction h : w.toNat using Nat.strongRecOn generalizing w with
  | _ k ih =>
    rw [bitLength_eq]
    by_cases hw : w = 0
    · subst hw; simp at h; subst h; simp
    · simp only [hw, if_false]
      have hpos : 0 < w.toNat := by
        apply Nat.pos_of_ne_zero; intro hz; exact hw (BitVec.eq_of_toNat_eq (by simpa using hz))
      have hsh : (w >>> (1 : Nat)).toNat = w.toNat / 2 := by
        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have hlt : (w >>> (1 : Nat)).toNat < k := by rw [hsh, ← h]; omega
      obtain ⟨h1, h2⟩ := ih _ hlt (w >>> (1 : Nat)) rfl
      rw [hsh] at h1 h2
      refine ⟨?_, ?_⟩
      · rw [Nat.pow_succ]; omega
      · intro n hn
        cases n with
        | zero => simp; omega
        | succ n =>
            have := h2 n (by omega)
            rw [Nat.pow_succ]; omega

/-- Exact HOL `bit_length_thm` (`stack_allocProofScript.sml:154-165`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "bit_length_thm"
  (words_as_type_indexed_bitvec)]
theorem bitLength_thm {width : Nat} [NeZero width] :
    ∀ w : BitVec width, (w >>> bitLength w = 0) ∧
      ∀ n, n < bitLength w → w >>> n ≠ 0 := by
  intro w
  obtain ⟨h1, h2⟩ := bitLength_spec w
  refine ⟨(ushiftRight_eq_zero_iff w _).2 h1, fun n hn h0 => ?_⟩
  have := (ushiftRight_eq_zero_iff w n).1 h0
  have := h2 n hn
  omega

/-- Exact HOL `word_lsr_dimindex` (`stack_allocProofScript.sml:167-171`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_lsr_dimindex"
  (words_as_type_indexed_bitvec)]
theorem word_lsr_dimindex {width : Nat} [NeZero width] {w : BitVec width} :
    w >>> width = 0 :=
  (ushiftRight_eq_zero_iff w width).2 w.isLt

/-- Exact HOL `bit_length_LESS_EQ_dimindex` (`stack_allocProofScript.sml:173-179`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "bit_length_LESS_EQ_dimindex"
  (words_as_type_indexed_bitvec)]
theorem bitLength_le_dimindex {width : Nat} [NeZero width] {w : BitVec width} :
    bitLength w ≤ width := by
  obtain ⟨_, h2⟩ := bitLength_spec w
  rcases Nat.lt_or_ge width (bitLength w) with hc | hc
  · have := h2 width hc
    have := w.isLt
    omega
  · exact hc

theorem msb_iff_le {width : Nat} [NeZero width] (w : BitVec width) :
    w.msb = true ↔ 2 ^ (width - 1) ≤ w.toNat := by
  rw [BitVec.msb_eq_decide]
  simp

/-- Exact HOL `shift_to_zero_word_msb` (`stack_allocProofScript.sml:181-190`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "shift_to_zero_word_msb"
  (words_as_type_indexed_bitvec)]
theorem shift_to_zero_word_msb {width : Nat} [NeZero width] {w : BitVec width} {n : Nat} :
    w >>> n = 0 ∧ w.msb = true → width ≤ n := by
  rintro ⟨h0, hm⟩
  have h1 := (ushiftRight_eq_zero_iff w n).1 h0
  have h2 := (msb_iff_le w).1 hm
  have hw : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  rcases Nat.lt_or_ge n width with hc | hc
  · have : 2 ^ n ≤ 2 ^ (width - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · exact hc

/-- Exact HOL `word_msb_IMP_bit_length` (`stack_allocProofScript.sml:192-200`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_msb_IMP_bit_length"
  (words_as_type_indexed_bitvec)]
theorem word_msb_IMP_bitLength {width : Nat} [NeZero width] :
    ∀ h : BitVec width, h.msb = true → bitLength h = width := by
  intro h hm
  have hle := bitLength_le_dimindex (w := h)
  have := shift_to_zero_word_msb ⟨(bitLength_thm h).1, hm⟩
  omega

/-- Exact HOL `get_bits_intro` (`stack_allocProofScript.sml:202-207`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "get_bits_intro"
  (words_as_type_indexed_bitvec)]
theorem getBits_intro {width : Nat} [NeZero width] {h : BitVec width} :
    h.msb = true → (List.range (width - 1)).map h.getLsbD = getBits h := by
  intro hm
  simp [getBits, word_msb_IMP_bitLength h hm]

/-- Exact HOL `bit_length_minus_1` (`stack_allocProofScript.sml:226-230`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "bit_length_minus_1"
  (words_as_type_indexed_bitvec)]
theorem bitLength_minus_1 {width : Nat} [NeZero width] {w : BitVec width} :
    w ≠ 0 → bitLength w - 1 = bitLength (w >>> (1 : Nat)) := by
  intro h
  rw [bitLength_eq w, if_neg h]
  omega

/-- Exact HOL `bit_length_eq_1` (`stack_allocProofScript.sml:232-244`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "bit_length_eq_1"
  (words_as_type_indexed_bitvec)]
theorem bitLength_eq_1 {width : Nat} [NeZero width] {w : BitVec width} :
    bitLength w = 1 ↔ w = 1 := by
  obtain ⟨h1, h2⟩ := bitLength_spec w
  have hw : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  have hone : (1 : BitVec width).toNat = 1 := by
    simp [BitVec.toNat_ofNat, Nat.one_mod_two_pow hw]
  constructor
  · intro hb
    rw [hb] at h1 h2
    have := h2 0 (by decide)
    apply BitVec.eq_of_toNat_eq
    rw [hone]; simp at h1 this; omega
  · intro hw1
    subst hw1
    rw [hone] at h1 h2
    rcases Nat.lt_or_ge (bitLength (1 : BitVec width)) 1 with hlt | hge
    · have : bitLength (1 : BitVec width) = 0 := by omega
      rw [this] at h1; simp at h1
    · rcases Nat.lt_or_ge 1 (bitLength (1 : BitVec width)) with hgt | hle
      · have := h2 1 hgt; simp at this
      · omega

/-- Exact HOL `word_and_one_eq_0_iff` (`stack_allocProofScript.sml:246-250`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_and_one_eq_0_iff"
  (words_as_type_indexed_bitvec)]
theorem word_and_one_eq_0_iff {width : Nat} [NeZero width] :
    ∀ w : BitVec width, (w &&& 1 = 0) ↔ ¬ w.getLsbD 0 = true := by
  intro w
  have hw : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  constructor
  · intro h h0
    rw [BitVec.getLsbD_eq_getElem hw] at h0
    have := congrArg (fun x => x[0]'hw) h
    simp [h0] at this
  · intro h
    ext i hi
    by_cases hi0 : i = 0
    · subst hi0; simpa [BitVec.getElem_and, BitVec.getLsbD_eq_getElem hw] using h
    · simp [BitVec.getElem_and, BitVec.getElem_one, hi0]

/-- Exact HOL `split_num_forall_to_10` (`stack_allocProofScript.sml:252-262`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "split_num_forall_to_10"]
theorem split_num_forall_to_10 {P : Nat → Prop} :
    (∀ x, P x) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 ∧ P 6 ∧ P 7 ∧ P 8 ∧ P 9 ∧
      ∀ x, 9 < x → P x := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7, h 8, h 9, fun x _ => h x⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h⟩ x
    match x with
    | 0 => exact h0 | 1 => exact h1 | 2 => exact h2 | 3 => exact h3 | 4 => exact h4
    | 5 => exact h5 | 6 => exact h6 | 7 => exact h7 | 8 => exact h8 | 9 => exact h9
    | x + 10 => exact h _ (by omega)

/-- Exact HOL `word_shift_not_0` (`stack_allocProofScript.sml:268-272`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_shift_not_0"
  (word_dimension_as_width := width)]
theorem wordShift_not_0 (width : Nat) [NeZero width] : wordShiftAmount width ≠ 0 := by
  unfold wordShiftAmount; split <;> decide

/-- Exact HOL `select_lower_lemma` (`stack_allocProofScript.sml:274-280`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "select_lower_lemma"
  (words_as_type_indexed_bitvec)]
theorem select_lower_lemma {width : Nat} [NeZero width] {n : Nat} {w : BitVec width} :
    gcWordBitsLow n w = (w <<< (width - n - 1)) >>> (width - n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [gcWordBitsLow, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have hlt : w.toNat % 2 ^ (n + 1) < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.mod_le _ _) w.isLt
  rw [Nat.mod_eq_of_lt hlt]
  by_cases hn : n + 1 ≤ width
  · have hk : 2 ^ width = 2 ^ (width - n - 1) * 2 ^ (n + 1) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hk, Nat.mul_comm w.toNat, Nat.mul_mod_mul_left,
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  · have hk : width - n - 1 = 0 := by omega
    have : w.toNat < 2 ^ (n + 1) :=
      Nat.lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    rw [hk, Nat.mod_eq_of_lt this]
    simp [Nat.mod_eq_of_lt w.isLt]

/-- Exact HOL `is_fwd_ptr_iff` (`stack_allocProofScript.sml:288-292`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "is_fwd_ptr_iff"
  (words_as_type_indexed_bitvec)]
theorem is_fwd_ptr_iff {width : Nat} [NeZero width] :
    ∀ w : WordLocW width, wordSemIsFwdPtr w = true ↔ ∃ v, w = .word v ∧ v &&& 3 = 0 := by
  intro w
  cases w <;> simp [wordSemIsFwdPtr]

/-- Exact HOL `isWord_thm` (`stack_allocProofScript.sml:294-298`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "isWord_thm"
  (words_as_type_indexed_bitvec)]
theorem isWord_thm {width : Nat} [NeZero width] :
    ∀ w : WordLocW width, wordSemIsWordLoc w = true ↔ ∃ v, w = .word v := by
  intro w
  cases w <;> simp [wordSemIsWordLoc]

/-- Exact HOL `lower_2w_eq` (`stack_allocProofScript.sml:300-305`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "lower_2w_eq"
  (words_as_type_indexed_bitvec)]
theorem lower_2w_eq {width : Nat} [NeZero width] :
    ∀ w : BitVec width, goodDimindex width → (w < 2 ↔ w = 0 ∨ w = 1) := by
  intro w hg
  rcases hg with rfl | rfl
  all_goals
    constructor
    · intro h
      change w.toNat < 2 at h
      have cases : w.toNat = 0 ∨ w.toNat = 1 := by omega
      rcases cases with zero | one
      · left
        apply BitVec.eq_of_toNat_eq
        simpa using zero
      · right
        apply BitVec.eq_of_toNat_eq
        simpa using one
    · rintro (rfl | rfl) <;> decide

/-- Exact HOL `EL_LENGTH_ADD_LEMMA` (`stack_allocProofScript.sml:307-312`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "EL_LENGTH_ADD_LEMMA" 307]
theorem EL_LENGTH_ADD_LEMMA {α : Type} [Nonempty α] {init old st1 : List α} {x : α} :
    holEl (init.length + old.length) (init ++ old ++ [x] ++ st1) = x := by
  rw [holEl_eq_getElem]
  · simp [List.getElem_append_right]
  · simp

/-- Exact HOL `EL_LENGTH_ADD_LEMMA` (second declaration,
`stack_allocProofScript.sml:347-351`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "EL_LENGTH_ADD_LEMMA" 347]
theorem EL_LENGTH_ADD_LEMMA' {α : Type} [Nonempty α] :
    ∀ (n : Nat) (xs : List α) (y : α) (ys : List α), xs.length = n → holEl n (xs ++ y :: ys) = y := by
  intro n xs y ys h
  subst h
  rw [holEl_eq_getElem]
  · simp
  · simp

/-- Exact HOL `LUPDATE_LENGTH_ADD_LEMMA` (`stack_allocProofScript.sml:314-319`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "LUPDATE_LENGTH_ADD_LEMMA"]
theorem LUPDATE_LENGTH_ADD_LEMMA {α : Type} {w x : α} {init old st1 : List α} :
    (init ++ old ++ [x] ++ st1).set (init.length + old.length) w =
      init ++ old ++ [w] ++ st1 := by
  simp [List.set_append_right]

/-- Exact HOL `word_msb_IFF_lsr_EQ_0` (`stack_allocProofScript.sml:321-325`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_msb_IFF_lsr_EQ_0"
  (words_as_type_indexed_bitvec)]
theorem word_msb_IFF_lsr_EQ_0 {width : Nat} [NeZero width] {h : BitVec width} :
    h.msb = true ↔ h >>> (width - 1) ≠ 0 := by
  rw [msb_iff_le, Ne, ushiftRight_eq_zero_iff]
  omega

/-- Exact HOL `bytes_in_word_word_shift_n2w` (`stack_allocProofScript.sml:353-362`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "bytes_in_word_word_shift_n2w"
  (words_as_type_indexed_bitvec)]
theorem bytesInWord_wordShift_n2w {width : Nat} [NeZero width] {n : Nat} :
    goodDimindex width ∧ (width / 8) * n < 2 ^ width →
      (wordSemBytesInWord * (BitVec.ofNat width n : BitVec width)) >>> wordShiftAmount width =
        (BitVec.ofNat width n : BitVec width) := by
  rintro ⟨hg, hlt⟩
  apply bytesInWord_wordShift
  refine ⟨hg, ?_⟩
  have hb : (wordSemBytesInWord : BitVec width).toNat = width / 8 := by
    rcases hg with rfl | rfl <;> rfl
  have hn : n < 2 ^ width := by
    rcases hg with rfl | rfl <;> omega
  rw [hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  exact hlt

/-- Exact HOL `word_sub_0_eq` (`stack_allocProofScript.sml:4536-4542`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_sub_0_eq"
  (words_as_type_indexed_bitvec)]
theorem word_sub_0_eq {width : Nat} [NeZero width] {w v : BitVec width} :
    ((-1 * w + v = 0) ↔ w = v) ∧ ((v + -1 * w = 0) ↔ w = v) := by
  have hneg : -1 * w = -w := by simp
  have e1 : -1 * w + v = v - w := by rw [hneg, BitVec.add_comm, BitVec.sub_eq_add_neg]
  have e2 : v + -1 * w = v - w := by rw [hneg, BitVec.sub_eq_add_neg]
  have key : v - w = 0 ↔ w = v := by
    constructor
    · intro h
      have := congrArg (· + w) h
      simp only [BitVec.sub_add_cancel] at this
      simpa [eq_comm] using this
    · rintro rfl; exact BitVec.sub_self _
  rw [e1, e2]
  exact ⟨key, key⟩

/-- Exact HOL `good_dimindex_byte_aligned_eq` (`stack_allocProofScript.sml:4544-4551`);
HOL `byte_aligned` is `gcByteAligned`. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "good_dimindex_byte_aligned_eq"
  (words_as_type_indexed_bitvec)]
theorem good_dimindex_byte_aligned_eq {width : Nat} [NeZero width] {w : BitVec width} :
    goodDimindex width →
      (gcByteAligned w = true ↔ (w &&& (if width = 32 then 3 else 7)) = 0) := by
  intro hg
  rcases hg with rfl | rfl
  · have he : Nat.log2 (32 / 8) = 2 := Nat.log2_two_pow (n := 2)
    simp only [gcByteAligned, decide_eq_true_eq, show (32 / 8 = 0) = False by decide, if_false,
      he, if_true, BitVec.toNat_eq, BitVec.toNat_and]
    have := w.isLt
    have hm : w.toNat &&& 3 = w.toNat % 4 := by
      simpa using Nat.and_two_pow_sub_one_eq_mod w.toNat 2
    simp at this ⊢
    omega
  · have he : Nat.log2 (64 / 8) = 3 := Nat.log2_two_pow (n := 3)
    simp only [gcByteAligned, decide_eq_true_eq, show (64 / 8 = 0) = False by decide, if_false,
      he, show (64 = 32) = False by decide, BitVec.toNat_eq, BitVec.toNat_and]
    have := w.isLt
    have hm : w.toNat &&& 7 = w.toNat % 8 := by
      simpa using Nat.and_two_pow_sub_one_eq_mod w.toNat 3
    simp at this ⊢
    omega

end Flapjack.Compiler.Backend.StackAlloc
