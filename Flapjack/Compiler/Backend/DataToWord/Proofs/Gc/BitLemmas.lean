module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordLemmas
public import Flapjack.Compiler.Backend.DataToWord.Header
public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

@[expose] public section

/-! Word and pointer bit lemmas of `data_to_word_gcProofScript.sml`
(lines 556-725). HOL `w ' i` is `BitVec.getLsbD`, `<<`/`>>>` are `<<<`/`>>>`,
`&&`/`||` are `&&&`/`|||` (HOL `||` is right associative, so `a || b || c` is
`a ||| (b ||| c)`), `n2w` is `BitVec.ofNat`, `ODD n` is `n % 2 = 1`,
`word_slice` (`(h '' l) w`) is the reviewed `holWordSlice`.
`is_fwd_ptr` is `wordSemIsFwdPtr`, `get_lowerbits` is `getLowerBits`, and
`shift_length`/`small_shift_length` are `shiftLength`/`smallShiftLength`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

open Flapjack Flapjack.Compiler.Backend.DataToWord

/-- A numeric `BitVec` literal has the `BitVec.ofNat` value. Flapjack proof
infrastructure; no HOL counterpart. -/
private theorem toNat_lit {width c : Nat} :
    (OfNat.ofNat c : BitVec width).toNat = c % 2 ^ width := rfl

/-- Exact HOL `one_and_or_1` (`data_to_word_gcProofScript.sml:556-560`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "one_and_or_1"
  (words_as_type_indexed_bitvec)]
theorem one_and_or_1 {width : Nat} [NeZero width] {w : BitVec width} :
    (1 : BitVec width) &&& (w ||| (1 : BitVec width)) = (1 : BitVec width) := by
  rw [BitVec.and_or_distrib_left, BitVec.and_self]
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_and]
  cases (1 : BitVec width)[i] <;> simp

/-- Exact HOL `one_and_or_3` (`data_to_word_gcProofScript.sml:562-566`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "one_and_or_3"
  (words_as_type_indexed_bitvec)]
theorem one_and_or_3 {width : Nat} [NeZero width] {w : BitVec width} :
    (3 : BitVec width) &&& (w ||| (3 : BitVec width)) = (3 : BitVec width) := by
  rw [BitVec.and_or_distrib_left, BitVec.and_self]
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_and]
  cases (3 : BitVec width)[i] <;> simp

/-- Exact HOL `ODD_not_zero` (`data_to_word_gcProofScript.sml:568-575`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "ODD_not_zero"
  (words_as_type_indexed_bitvec)]
theorem ODD_not_zero {width : Nat} [NeZero width] {n : Nat} :
    n % 2 = 1 → BitVec.ofNat width n ≠ (0 : BitVec width) := by
  intro hn heq
  have hw : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  have h := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, toNat_lit, Nat.zero_mod] at h
  have h2 : 2 ∣ 2 ^ width := by simpa using Nat.pow_dvd_pow 2 hw
  have := Nat.mod_mod_of_dvd n h2
  omega

/-- Exact HOL `three_not_0` (`data_to_word_gcProofScript.sml:577-581`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "three_not_0"
  (words_as_type_indexed_bitvec)]
theorem three_not_0 {width : Nat} [NeZero width] : (3 : BitVec width) ≠ 0 :=
  ODD_not_zero (n := 3) rfl

/-- Exact HOL `three_and_shift_2` (`data_to_word_gcProofScript.sml:585-589`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "three_and_shift_2"
  (words_as_type_indexed_bitvec)]
theorem three_and_shift_2 {width : Nat} [NeZero width] {w : BitVec width} :
    (3 : BitVec width) &&& w <<< (2 : Nat) = (0 : BitVec width) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_lit (c := 0), Nat.zero_mod]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.zero_testBit, BitVec.toNat_shiftLeft, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  by_cases hj : 2 ≤ j
  · rw [toNat_lit, Nat.testBit_lt_two_pow (Nat.lt_of_le_of_lt (Nat.mod_le _ _)
      (Nat.lt_of_lt_of_le (by decide : 3 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hj)))]
    simp
  · simp [hj]

/-- Exact HOL `shift_to_zero` (`data_to_word_gcProofScript.sml:591-595`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "shift_to_zero"
  (words_as_type_indexed_bitvec)]
theorem shift_to_zero {width : Nat} [NeZero width] :
    (3 : BitVec width) >>> (2 : Nat) = (0 : BitVec width) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_lit, toNat_lit (c := 0), Nat.zero_mod,
    Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by decide))

/-- Exact HOL `shift_around_under_big_shift` (`data_to_word_gcProofScript.sml:597-601`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml"
  "shift_around_under_big_shift" (words_as_type_indexed_bitvec)]
theorem shift_around_under_big_shift {width : Nat} [NeZero width] :
    ∀ (w : BitVec width) (n k : Nat), n ≤ k → w <<< n >>> n <<< k = w <<< k := by
  intro w n k h
  ext i hi
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight]
  by_cases hk : i < k
  · simp [hk]
  · simp only [hk, decide_false, Bool.not_false, Bool.true_and]
    rw [BitVec.getLsbD_shiftLeft]
    have h1 : n + (i - k) < width := by omega
    simp [h1, show ¬ (n + (i - k) < n) by omega, show n + (i - k) - n = i - k by omega]
    exact BitVec.getLsbD_eq_getElem (by omega)

/-- Exact HOL `shift_length_NOT_ZERO` (`data_to_word_gcProofScript.sml:609-613`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "shift_length_NOT_ZERO"]
theorem shift_length_NOT_ZERO {conf : Config} : shiftLength conf ≠ 0 := by
  simp only [shiftLength]
  omega

/-- Exact HOL `one_lsr_shift_length` (`data_to_word_gcProofScript.sml:622-627`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "one_lsr_shift_length"
  (words_as_type_indexed_bitvec)]
theorem one_lsr_shift_length {width : Nat} [NeZero width] {conf : Config} :
    (1 : BitVec width) >>> shiftLength conf = (0 : BitVec width) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_lit, toNat_lit (c := 0), Nat.zero_mod,
    Nat.shiftRight_eq_div_pow]
  apply Nat.div_eq_of_lt
  have h2 : 2 ≤ 2 ^ shiftLength conf := by
    have := shift_length_NOT_ZERO (conf := conf)
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ shiftLength conf := Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_of_lt_of_le (by decide) h2)

/-- Exact HOL `is_fws_ptr_OR_3` (`data_to_word_gcProofScript.sml:646-651`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "is_fws_ptr_OR_3"
  (words_as_type_indexed_bitvec)]
theorem is_fws_ptr_OR_3 {width : Nat} [NeZero width] {w : BitVec width} :
    wordSemIsFwdPtr (WordLocW.word (w <<< (2 : Nat))) = true ∧
      ¬ wordSemIsFwdPtr (WordLocW.word (w ||| (3 : BitVec width))) = true := by
  simp only [wordSemIsFwdPtr, decide_eq_true_eq]
  refine ⟨by rw [BitVec.and_comm]; exact three_and_shift_2, ?_⟩
  rw [BitVec.and_comm, one_and_or_3]
  exact three_not_0

/-- The common body of the three `is_fws_ptr_OR_*` theorems: or-ing a constant
whose low bit is set yields a word that is not a forwarding pointer. Flapjack
proof infrastructure; no HOL counterpart. -/
private theorem not_fwd_of_or_odd {width : Nat} [NeZero width] {w : BitVec width} {c : Nat}
    (hc : c % 2 = 1) : ¬ wordSemIsFwdPtr (WordLocW.word (w ||| BitVec.ofNat width c)) = true := by
  simp only [wordSemIsFwdPtr, decide_eq_true_eq]
  intro heq
  have hw : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  have h := congrArg (fun x => x.toNat.testBit 0) heq
  have h2 : 2 ∣ 2 ^ width := by simpa using Nat.pow_dvd_pow 2 hw
  rw [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ofNat, toNat_lit (c := 3),
    toNat_lit (c := 0), Nat.zero_mod, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit,
    Nat.testBit_zero (c % 2 ^ width), Nat.testBit_zero (3 % 2 ^ width),
    Nat.mod_mod_of_dvd _ h2, Nat.mod_mod_of_dvd _ h2, hc] at h
  simp at h

/-- Exact HOL `is_fws_ptr_OR_15` (`data_to_word_gcProofScript.sml:653-659`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "is_fws_ptr_OR_15"
  (words_as_type_indexed_bitvec)]
theorem is_fws_ptr_OR_15 {width : Nat} [NeZero width] {w : BitVec width} :
    ¬ wordSemIsFwdPtr (WordLocW.word (w ||| (15 : BitVec width))) = true :=
  not_fwd_of_or_odd (c := 15) rfl

/-- Exact HOL `is_fws_ptr_OR_10111` (`data_to_word_gcProofScript.sml:661-667`);
HOL `0b10111w` is the word literal `23`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "is_fws_ptr_OR_10111"
  (words_as_type_indexed_bitvec)]
theorem is_fws_ptr_OR_10111 {width : Nat} [NeZero width] {w : BitVec width} :
    ¬ wordSemIsFwdPtr (WordLocW.word (w ||| (23 : BitVec width))) = true :=
  not_fwd_of_or_odd (c := 23) rfl

/-- Exact HOL `is_fws_ptr_OR_7` (`data_to_word_gcProofScript.sml:669-675`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "is_fws_ptr_OR_7"
  (words_as_type_indexed_bitvec)]
theorem is_fws_ptr_OR_7 {width : Nat} [NeZero width] {w : BitVec width} :
    ¬ wordSemIsFwdPtr (WordLocW.word (w ||| (7 : BitVec width))) = true :=
  not_fwd_of_or_odd (c := 7) rfl

/-- Exact HOL `LE_DIV_LT_IMP` (`data_to_word_gcProofScript.sml:689-696`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "LE_DIV_LT_IMP"]
theorem LE_DIV_LT_IMP {n l m k : Nat} : n ≤ l / 2 ^ m ∧ k < n → k * 2 ^ m < l := by
  rintro ⟨h1, h2⟩
  have hp := Nat.two_pow_pos m
  have h3 : (k + 1) * 2 ^ m ≤ l :=
    Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) (Nat.div_mul_le_self l (2 ^ m))
  rw [Nat.succ_mul] at h3
  exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hp) h3

/-- Exact HOL `word_slice_or` (`data_to_word_gcProofScript.sml:706-713`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_slice_or"
  (words_as_type_indexed_bitvec)]
theorem word_slice_or {width : Nat} [NeZero width] {k n : Nat} {w v : BitVec width} :
    holWordSlice k n (w ||| v) = holWordSlice k n w ||| holWordSlice k n v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [holWordSlice, getLsbD_holFcpWord, BitVec.getLsbD_or]
  cases decide (i < width) <;> cases decide (n ≤ i ∧ i ≤ min k (width - 1)) <;> simp

/-- Exact HOL `word_slice_lsl_eq_0` (`data_to_word_gcProofScript.sml:715-719`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_slice_lsl_eq_0"
  (words_as_type_indexed_bitvec)]
theorem word_slice_lsl_eq_0 {width : Nat} [NeZero width] {k n : Nat} {w : BitVec width} :
    holWordSlice k n (w <<< (k + 1)) = (0 : BitVec width) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [holWordSlice, getLsbD_holFcpWord, BitVec.getLsbD_shiftLeft]
  by_cases h : i ≤ k
  · simp [show i < k + 1 by omega]
  · simp [show ¬ (n ≤ i ∧ i ≤ min k (width - 1)) by omega]

/-- Exact HOL `word_slice_2_3_eq_0` (`data_to_word_gcProofScript.sml:721-725`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_slice_2_3_eq_0"
  (words_as_type_indexed_bitvec)]
theorem word_slice_2_3_eq_0 {width : Nat} [NeZero width] {n : Nat} :
    holWordSlice n 2 (3 : BitVec width) = (0 : BitVec width) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [holWordSlice, getLsbD_holFcpWord]
  by_cases h : 2 ≤ i
  · have : Nat.testBit 3 i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 3 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) h))
    simp [BitVec.getLsbD_ofNat, this]
  · simp [h]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
