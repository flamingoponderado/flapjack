import Flapjack.Misc.GetByteSetByte
import Mathlib.Tactic.IntervalCases

/-! Original word-alignment and byte-reassembly helpers used by `Inst_lemma`
(lab_to_targetProofScript.sml:1786-2003, 2146-2168). The HOL hypotheses
`dimindex (:'a) = 32`/`64` are kept as equations on the positive BitVec
width; `aligned`, `byte_align` and `w2w` are the reviewed `holAligned`,
`holByteAlign` and `BitVec.setWidth`. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "MULT_ADD_LESS_MULT"]
theorem mult_add_less_mult (m n k l j : Nat) :
    m < l ∧ n < k ∧ j ≤ k → m * j + n < l * k := by
  rintro ⟨h1, h2, h3⟩
  have : m * j ≤ m * k := Nat.mul_le_mul_left m h3
  have : (m + 1) * k ≤ l * k := Nat.mul_le_mul_right k h1
  rw [Nat.succ_mul] at this
  omega

/-- `aligned p w` is divisibility of the numeral by `2 ^ p`; Flapjack
infrastructure (HOL `aligned_w2n`). -/
theorem holAligned_iff {width : Nat} [NeZero width] (k : Nat) (x : BitVec width) :
    holAligned k x = true ↔ x.toNat % 2 ^ k = 0 := by
  have hlt : x.toNat / 2 ^ k * 2 ^ k < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) x.isLt
  simp only [holAligned, holAlign_eq_div, decide_eq_true_eq, BitVec.toNat_eq,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  constructor
  · intro h
    have := Nat.div_add_mod x.toNat (2 ^ k)
    rw [Nat.mul_comm] at this
    omega
  · intro h
    have := Nat.div_add_mod x.toNat (2 ^ k)
    rw [Nat.mul_comm] at this
    omega

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "aligned_IMP_ADD_LESS_dimword" (words_as_type_indexed_bitvec)]
theorem aligned_imp_add_less_dimword {width : Nat} [NeZero width] (k : Nat)
    (x : BitVec width) :
    holAligned k x = true ∧ k ≤ width → x.toNat + (2 ^ k - 1) < 2 ^ width := by
  rintro ⟨ha, hk⟩
  rw [holAligned_iff] at ha
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hx := x.isLt
  have hdiv : 2 ^ width = 2 ^ (width - k) * 2 ^ k := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hk]
  obtain ⟨q, hq⟩ : 2 ^ k ∣ x.toNat := Nat.dvd_of_mod_eq_zero ha
  rw [hq, Nat.mul_comm] at hx ⊢
  rw [hdiv] at hx ⊢
  have hq' : q < 2 ^ (width - k) := Nat.lt_of_mul_lt_mul_right hx
  have := mult_add_less_mult q (2 ^ k - 1) (2 ^ k) (2 ^ (width - k)) (2 ^ k)
    ⟨hq', by omega, Nat.le_refl _⟩
  exact this

/-- `byte_align` at width 32 clears the two low bits; Flapjack infrastructure. -/
theorem holByteAlign32_toNat (x : BitVec 32) :
    (holByteAlign x).toNat = x.toNat / 4 * 4 :=
  holByteAlign_toNat (Or.inl rfl) x

/-- `byte_align` at width 64 clears the three low bits; Flapjack infrastructure. -/
theorem holByteAlign64_toNat (x : BitVec 64) :
    (holByteAlign x).toNat = x.toNat / 8 * 8 :=
  holByteAlign_toNat (Or.inr rfl) x

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "aligned_2_imp"
  (words_as_type_indexed_bitvec)]
theorem aligned_2_imp {width : Nat} [NeZero width] (x : BitVec width) :
    holAligned 2 x = true ∧ width = 32 →
    holByteAlign x = x ∧ holByteAlign (x + 1) = x ∧ holByteAlign (x + 2) = x ∧
      holByteAlign (x + 3) = x := by
  rintro ⟨ha, rfl⟩
  rw [holAligned_iff] at ha
  have hx := x.isLt
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    rw [holByteAlign32_toNat] <;> bv_omega

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "aligned_2_not_eq"
  (words_as_type_indexed_bitvec)]
theorem aligned_2_not_eq {width : Nat} [NeZero width] (x a : BitVec width) :
    holAligned 2 x = true ∧ width = 32 ∧ x ≠ holByteAlign a →
    x ≠ a ∧ x + 1 ≠ a ∧ x + 2 ≠ a ∧ x + 3 ≠ a := by
  rintro ⟨ha, hw, hne⟩
  have h := aligned_2_imp x ⟨ha, hw⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · exact hne h.1.symm
  · exact hne h.2.1.symm
  · exact hne h.2.2.1.symm
  · exact hne h.2.2.2.symm

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "aligned_3_imp"
  (words_as_type_indexed_bitvec)]
theorem aligned_3_imp {width : Nat} [NeZero width] (x : BitVec width) :
    holAligned 3 x = true ∧ width = 64 →
    holByteAlign x = x ∧ holByteAlign (x + 1) = x ∧ holByteAlign (x + 2) = x ∧
      holByteAlign (x + 3) = x ∧ holByteAlign (x + 4) = x ∧ holByteAlign (x + 5) = x ∧
      holByteAlign (x + 6) = x ∧ holByteAlign (x + 7) = x := by
  rintro ⟨ha, rfl⟩
  rw [holAligned_iff] at ha
  have hx := x.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    rw [holByteAlign64_toNat] <;> bv_omega

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "aligned_3_not_eq"
  (words_as_type_indexed_bitvec)]
theorem aligned_3_not_eq {width : Nat} [NeZero width] (x a : BitVec width) :
    holAligned 3 x = true ∧ width = 64 ∧ x ≠ holByteAlign a →
    x ≠ a ∧ x + 1 ≠ a ∧ x + 2 ≠ a ∧ x + 3 ≠ a ∧ x + 4 ≠ a ∧ x + 5 ≠ a ∧ x + 6 ≠ a ∧
      x + 7 ≠ a := by
  rintro ⟨ha, hw, hne⟩
  have h := aligned_3_imp x ⟨ha, hw⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · exact hne h.1.symm
  · exact hne h.2.1.symm
  · exact hne h.2.2.1.symm
  · exact hne h.2.2.2.1.symm
  · exact hne h.2.2.2.2.1.symm
  · exact hne h.2.2.2.2.2.1.symm
  · exact hne h.2.2.2.2.2.2.1.symm
  · exact hne h.2.2.2.2.2.2.2.symm

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "dimword_eq_32_imp_or_bytes" (words_as_type_indexed_bitvec)]
theorem dimword_eq_32_imp_or_bytes {width : Nat} [NeZero width] (x : BitVec width) :
    width = 32 →
    ((x.setWidth 8).setWidth width |||
      (((x >>> 8).setWidth 8).setWidth width <<< 8 |||
      (((x >>> 16).setWidth 8).setWidth width <<< 16 |||
      ((x >>> 24).setWidth 8).setWidth width <<< 24))) = x := by
  rintro rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "dimword_eq_64_imp_or_bytes" (words_as_type_indexed_bitvec)]
theorem dimword_eq_64_imp_or_bytes {width : Nat} [NeZero width] (x : BitVec width) :
    width = 64 →
    ((x.setWidth 8).setWidth width |||
      (((x >>> 8).setWidth 8).setWidth width <<< 8 |||
      (((x >>> 16).setWidth 8).setWidth width <<< 16 |||
      (((x >>> 24).setWidth 8).setWidth width <<< 24 |||
      (((x >>> 32).setWidth 8).setWidth width <<< 32 |||
      (((x >>> 40).setWidth 8).setWidth width <<< 40 |||
      (((x >>> 48).setWidth 8).setWidth width <<< 48 |||
      ((x >>> 56).setWidth 8).setWidth width <<< 56))))))) = x := by
  rintro rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "byte_align_32_eq"
  (words_as_type_indexed_bitvec)]
theorem byte_align_32_eq {width : Nat} [NeZero width] (a : BitVec width) :
    width = 32 → holByteAlign a + BitVec.ofNat width (a.toNat % 4) = a := by
  rintro rfl
  have hx := a.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, holByteAlign32_toNat]
  bv_omega

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "byte_align_64_eq"
  (words_as_type_indexed_bitvec)]
theorem byte_align_64_eq {width : Nat} [NeZero width] (a : BitVec width) :
    width = 64 → holByteAlign a + BitVec.ofNat width (a.toNat % 8) = a := by
  rintro rfl
  have hx := a.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, holByteAlign64_toNat]
  bv_omega

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "byte_align_32_IMP"
  (words_as_type_indexed_bitvec)]
theorem byte_align_32_imp {width : Nat} [NeZero width] (a : BitVec width) :
    width = 32 →
    (holByteAlign a = a → a.toNat % 4 = 0) ∧
    (holByteAlign a + (1 : BitVec width) = a → a.toNat % 4 = 1) ∧
    (holByteAlign a + (2 : BitVec width) = a → a.toNat % 4 = 2) ∧
    (holByteAlign a + (3 : BitVec width) = a → a.toNat % 4 = 3) := by
  rintro rfl
  have hx := a.isLt
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> have h' := congrArg BitVec.toNat h <;>
    simp only [BitVec.toNat_add, holByteAlign32_toNat] at h' <;> bv_omega

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "MOD4_CASES"]
theorem mod4_cases (n : Nat) : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
  omega

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "byte_align_32_CASES"
  (words_as_type_indexed_bitvec)]
theorem byte_align_32_cases {width : Nat} [NeZero width] (a : BitVec width) :
    width = 32 →
    holByteAlign a + (3 : BitVec width) = a ∨ holByteAlign a + (2 : BitVec width) = a ∨
      holByteAlign a + (1 : BitVec width) = a ∨ holByteAlign a = a := by
  intro hw
  have h := byte_align_32_eq a hw
  subst hw
  rcases mod4_cases a.toNat with hm | hm | hm | hm <;> rw [hm] at h <;> simp_all

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "MOD8_CASES"]
theorem mod8_cases (n : Nat) :
    n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨
      n % 8 = 7 := by
  omega

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "byte_align_64_CASES"
  (words_as_type_indexed_bitvec)]
theorem byte_align_64_cases {width : Nat} [NeZero width] (a : BitVec width) :
    width = 64 →
    holByteAlign a + (7 : BitVec width) = a ∨ holByteAlign a + (6 : BitVec width) = a ∨
      holByteAlign a + (5 : BitVec width) = a ∨ holByteAlign a + (4 : BitVec width) = a ∨
      holByteAlign a + (3 : BitVec width) = a ∨ holByteAlign a + (2 : BitVec width) = a ∨
      holByteAlign a + (1 : BitVec width) = a ∨ holByteAlign a = a := by
  intro hw
  have h := byte_align_64_eq a hw
  subst hw
  rcases mod8_cases a.toNat with hm | hm | hm | hm | hm | hm | hm | hm <;>
    rw [hm] at h <;> simp_all

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "byte_align_64_IMP"
  (words_as_type_indexed_bitvec)]
theorem byte_align_64_imp {width : Nat} [NeZero width] (a : BitVec width) :
    width = 64 →
    (holByteAlign a + (7 : BitVec width) = a → a.toNat % 8 = 7) ∧
    (holByteAlign a + (6 : BitVec width) = a → a.toNat % 8 = 6) ∧
    (holByteAlign a + (5 : BitVec width) = a → a.toNat % 8 = 5) ∧
    (holByteAlign a + (4 : BitVec width) = a → a.toNat % 8 = 4) ∧
    (holByteAlign a + (3 : BitVec width) = a → a.toNat % 8 = 3) ∧
    (holByteAlign a + (2 : BitVec width) = a → a.toNat % 8 = 2) ∧
    (holByteAlign a + (1 : BitVec width) = a → a.toNat % 8 = 1) ∧
    (holByteAlign a = a → a.toNat % 8 = 0) := by
  rintro rfl
  have hx := a.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> have h' := congrArg BitVec.toNat h <;>
    simp only [BitVec.toNat_add, holByteAlign64_toNat] at h' <;> bv_omega

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "align2_not_align3_4w"
  (words_as_type_indexed_bitvec)]
theorem align2_not_align3_4w {width : Nat} [NeZero width] (x : BitVec width) :
    ¬ holAligned 3 x = true ∧ holAligned 2 x = true ∧ width = 64 →
    x = holByteAlign x + 4 ∧ x + 1 = holByteAlign x + 5 ∧ x + 2 = holByteAlign x + 6 ∧
      x + 3 = holByteAlign x + 7 := by
  rintro ⟨h3, h2, rfl⟩
  rw [holAligned_iff] at h3 h2
  have hx := x.isLt
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_add, holByteAlign64_toNat] <;> bv_omega

end Flapjack.Compiler.Backend.LabToTarget
