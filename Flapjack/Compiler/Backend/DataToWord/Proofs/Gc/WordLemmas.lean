module

public import Flapjack.Misc.Alignment
public import Flapjack.Misc.Multiword

@[expose] public section

/-! `data_to_word_gcProofScript.sml` opening word lemmas (lines 38-115).
HOL's `>>>` and `<<` on words are Lean's `BitVec` logical shifts `>>>` and
`<<<`, HOL's arithmetic shift `>>` (`word_asr`) is `BitVec.sshiftRight`, the
word index `w ' i` is `BitVec.getLsbD`, `n2w` is `BitVec.ofNat` and `w2n` is
`BitVec.toNat`. HOL's integer `ABS i` is `(i.natAbs : Int)`, which agrees with
`INT_ABS i = if i < 0 then -i else i` on every integer. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

open Flapjack

/-- Exact HOL `word_asr_dimindex` (`data_to_word_gcProofScript.sml:49-54`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_asr_dimindex"
  (words_as_type_indexed_bitvec)]
theorem word_asr_dimindex {width : Nat} [NeZero width] :
    ∀ (w : BitVec width) (n : Nat), width ≤ n →
      w.sshiftRight n = w.sshiftRight (width - 1) := by
  intro w n h
  have hw : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_sshiftRight]
  by_cases hi0 : i = 0
  · subst hi0
    simp only [Nat.add_zero]
    rw [if_neg (by omega), if_pos (by omega), BitVec.msb_eq_getLsbD_last]
  · rw [if_neg (by omega), if_neg (by omega)]

/-- Exact HOL `WORD_MUL_BIT0` (`data_to_word_gcProofScript.sml:56-61`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "WORD_MUL_BIT0"
  (words_as_type_indexed_bitvec)]
theorem WORD_MUL_BIT0 {width : Nat} [NeZero width] :
    ∀ (a b : BitVec width),
      (a * b).getLsbD 0 = true ↔ a.getLsbD 0 = true ∧ b.getLsbD 0 = true := by
  intro a b
  have hw : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  simp only [BitVec.getLsbD, BitVec.toNat_mul, Nat.testBit_zero, decide_eq_true_eq]
  have hpow : 2 ∣ 2 ^ width := by simpa using Nat.pow_dvd_pow 2 hw
  rw [Nat.mod_mod_of_dvd _ hpow, Nat.mul_mod]
  rcases Nat.mod_two_eq_zero_or_one a.toNat with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b.toNat with hb | hb <;> simp [ha, hb]

/-- Exact HOL `word_lsl_index` (`data_to_word_gcProofScript.sml:63-68`); the
HOL free variables `i`, `w` and `n` are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_lsl_index"
  (words_as_type_indexed_bitvec)]
theorem word_lsl_index {width : Nat} [NeZero width] {i : Nat} {w : BitVec width} {n : Nat} :
    i < width → ((w <<< n).getLsbD i = true ↔ n ≤ i ∧ w.getLsbD (i - n) = true) := by
  intro hi
  simp only [BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]

/-- Exact HOL `word_lsr_index` (`data_to_word_gcProofScript.sml:70-75`); the
HOL free variables `i`, `w` and `n` are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_lsr_index"
  (words_as_type_indexed_bitvec)]
theorem word_lsr_index {width : Nat} [NeZero width] {i : Nat} {w : BitVec width} {n : Nat} :
    i < width →
      ((w >>> n).getLsbD i = true ↔ i + n < width ∧ w.getLsbD (i + n) = true) := by
  intro _
  simp only [BitVec.getLsbD_ushiftRight]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := BitVec.lt_of_getLsbD h
      omega
    · rw [Nat.add_comm]; exact h
  · intro h
    rw [Nat.add_comm]; exact h.2

/-- Full original `lsr_lsl` (`data_to_word_gcProofScript.sml:77-81`):
`∀w n. aligned n w ⇒ (w >>> n << n = w)`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "lsr_lsl"
  (words_as_type_indexed_bitvec)]
theorem lsrLsl {width : Nat} [NeZero width] :
    ∀ (w : BitVec width) (n : Nat), holAligned n w = true → (w >>> n) <<< n = w := by
  intro w n h
  simp only [holAligned, decide_eq_true_eq] at h
  rw [← holAlign_eq_shift, h]

/-- Exact HOL `word_index_test` (`data_to_word_gcProofScript.sml:83-87`); the
HOL free variables `n` and `w` are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_index_test"
  (words_as_type_indexed_bitvec)]
theorem word_index_test {width : Nat} [NeZero width] {n : Nat} {w : BitVec width} :
    n < width → (w.getLsbD n = true ↔ (w &&& BitVec.ofNat width (2 ^ n)) ≠ 0) := by
  intro hn
  constructor
  · intro h heq
    have := congrArg (fun x => x.getLsbD n) heq
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_self, h,
      decide_true, hn, Bool.true_and] at this
    simp at this
  · intro h
    apply Classical.byContradiction
    intro hne
    apply h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
    by_cases hin : n = i
    · subst hin; simp_all
    · simp [hin]

/-- Exact HOL `word_and_one_eq_0_iff` (`data_to_word_gcProofScript.sml:89-93`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_and_one_eq_0_iff"
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

/-- Exact HOL `word_index_0` (`data_to_word_gcProofScript.sml:95-99`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_index_0"
  (words_as_type_indexed_bitvec)]
theorem word_index_0 {width : Nat} [NeZero width] :
    ∀ w : BitVec width, w.getLsbD 0 = true ↔ ¬ (1 &&& w = 0) := by
  intro w
  rw [BitVec.and_comm, word_and_one_eq_0_iff, Classical.not_not]

/-- Exact HOL `ABS_w2n` (`data_to_word_gcProofScript.sml:101-105`); the HOL
free variable `w` is universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "ABS_w2n"
  (words_as_type_indexed_bitvec)]
theorem ABS_w2n {width : Nat} [NeZero width] {w : BitVec width} :
    (((w.toNat : Int).natAbs : Nat) : Int) = (w.toNat : Int) := by
  simp

/-- Exact HOL `n2mw_w2n` (`data_to_word_gcProofScript.sml:107-114`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "n2mw_w2n"
  (words_as_type_indexed_bitvec)]
theorem n2mw_w2n {width : Nat} [NeZero width] :
    ∀ w : BitVec width,
      Misc.Multiword.n2mw (width := width) w.toNat = if w = 0 then [] else [w] := by
  intro w
  have hlt := w.isLt
  have hpos : 0 < 2 ^ width := Nat.two_pow_pos width
  by_cases hw : w = 0
  · subst hw
    rw [Misc.Multiword.n2mw]
    simp
  · have hn : w.toNat ≠ 0 := by
      intro h; exact hw (BitVec.eq_of_toNat_eq (by simpa using h))
    rw [Misc.Multiword.n2mw, if_neg hn, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt,
      Misc.Multiword.n2mw, if_pos rfl, if_neg hw]
    simp

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
