import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Number
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
import Mathlib.Tactic.NormNum

/-! Signed comparisons of data-language small integers. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- The immediate integer encoding is conversion of four times the integer. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "Smallnum_i2w"
  (words_as_type_indexed_bitvec)]
theorem smallnum_i2w {width : Nat} [NeZero width] (i : Int) :
    (smallnum i : BitVec width) = BitVec.ofInt width (4 * i) := by
  rw [smallnum_eq_inlined]
  cases i with
  | ofNat n => simp [Int.natAbs, BitVec.ofInt_mul, BitVec.ofNat_mul, Int.not_lt.mpr (Int.natCast_nonneg n)]
  | negSucc n =>
      have neg : Int.negSucc n < 0 := by omega
      simp only [neg, ↓reduceIte, Int.natAbs_negSucc]
      have eq : (4 : Int) * Int.negSucc n = -((4 * (n + 1) : Nat) : Int) := by omega
      rw [eq, BitVec.ofInt_neg, BitVec.ofInt_natCast]

/-- Small-integer encoding stays within the signed word range. This is
Flapjack arithmetic infrastructure for the source's word comparison proof. -/
theorem smallnum_signedBounds {width : Nat} [NeZero width] (good : goodDimindex width)
    (i : Int) (small : smallInt width i) :
    - (2 : Int) ^ (width - 1) ≤ 4 * i ∧ 4 * i < 2 ^ (width - 1) := by
  rcases good with h | h <;> subst width <;> norm_num [smallInt] at small ⊢ <;> omega

/-- Signed word comparison of two immediate integers matches integer order. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "num_less_thm"
  (words_as_type_indexed_bitvec)]
theorem numLessThm {width : Nat} [NeZero width] (i1 i2 : Int) :
    goodDimindex width ∧ smallInt width i1 ∧ smallInt width i2 →
      (i1 < i2 ↔ (smallnum i1 : BitVec width).slt (smallnum i2) = true) := by
  rintro ⟨good, small1, small2⟩
  have bounds1 := smallnum_signedBounds good i1 small1
  have bounds2 := smallnum_signedBounds good i2 small2
  have pos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  rw [BitVec.slt_eq_decide, decide_eq_true_eq]
  rw [smallnum_i2w, smallnum_i2w, BitVec.toInt_ofInt_eq_self pos bounds1.1 bounds1.2,
    BitVec.toInt_ofInt_eq_self pos bounds2.1 bounds2.2]
  omega

/-- The signed comparison of related small-integer words matches the source comparison. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Number_LESS"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_numberLess {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i1 i2 : Int) (w1 w2 : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain
      ((.number i1, w1) :: (.number i2, w2) :: vars) ∧
      smallInt width i1 ∧ smallInt width i2 ∧ goodDimindex width →
    ∃ v1 v2 : BitVec width, w1 = .word v1 ∧ w2 = .word v2 ∧
      (v1.slt v2 = true ↔ i1 < i2) := by
  rintro ⟨inv, small1, small2, good⟩
  have first := memoryRel_numberImp conf bigEndian next refs space store memory domain i1 w1
    ((.number i2, w2) :: vars) ⟨good, small1, inv⟩
  have tail := memoryRel_tl conf bigEndian next refs space store memory domain
    (.number i1, w1) ((.number i2, w2) :: vars) inv
  have second := memoryRel_numberImp conf bigEndian next refs space store memory domain i2 w2 vars
    ⟨good, small2, tail⟩
  exact ⟨smallnum i1, smallnum i2, first, second, (numLessThm i1 i2 ⟨good, small1, small2⟩).symm⟩

/-- Immediate encodings are injective in the small-integer range. This is
Flapjack arithmetic infrastructure for the source equality proof. -/
theorem smallnum_injective {width : Nat} [NeZero width] (good : goodDimindex width)
    (i1 i2 : Int) (small1 : smallInt width i1) (small2 : smallInt width i2)
    (equal : smallnum (width := width) i1 = smallnum i2) : i1 = i2 := by
  have bounds1 := smallnum_signedBounds good i1 small1
  have bounds2 := smallnum_signedBounds good i2 small2
  have pos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  have signed := congrArg BitVec.toInt equal
  rw [smallnum_i2w, smallnum_i2w, BitVec.toInt_ofInt_eq_self pos bounds1.1 bounds1.2,
    BitVec.toInt_ofInt_eq_self pos bounds2.1 bounds2.2] at signed
  omega

/-- Related numbers compare equal precisely when their source integers agree,
provided at least one of them is a small integer. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Number_EQ"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_numberEq {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i1 i2 : Int) (w1 w2 : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain
      ((.number i1, w1) :: (.number i2, w2) :: vars) ∧
      (smallInt width i1 ∨ smallInt width i2) ∧ goodDimindex width →
    ∃ v1 v2 : BitVec width, w1 = .word v1 ∧ w2 = .word v2 ∧ (v1 = v2 ↔ i1 = i2) := by
  rintro ⟨inv, either, good⟩
  have tail := memoryRel_tl conf bigEndian next refs space store memory domain
    (.number i1, w1) ((.number i2, w2) :: vars) inv
  obtain ⟨v1, eq1, bit1⟩ := memoryRel_anyNumberImp conf bigEndian next refs space store memory domain
    i1 w1 ((.number i2, w2) :: vars) ⟨good, inv⟩
  obtain ⟨v2, eq2, bit2⟩ := memoryRel_anyNumberImp conf bigEndian next refs space store memory domain
    i2 w2 vars ⟨good, tail⟩
  refine ⟨v1, v2, eq1, eq2, ?_⟩
  constructor
  · intro equal
    by_cases small1 : smallInt width i1
    · by_cases small2 : smallInt width i2
      · have h1 := memoryRel_numberImp conf bigEndian next refs space store memory domain i1 w1
          ((.number i2, w2) :: vars) ⟨good, small1, inv⟩
        have h2 := memoryRel_numberImp conf bigEndian next refs space store memory domain i2 w2 vars
          ⟨good, small2, tail⟩
        have enc1 : v1 = smallnum i1 := WordLocW.word.inj (eq1.symm.trans h1)
        have enc2 : v2 = smallnum i2 := WordLocW.word.inj (eq2.symm.trans h2)
        apply smallnum_injective good i1 i2 small1 small2
        exact enc1.symm.trans (equal.trans enc2)
      · have clear : v1.getLsbD 0 = false := by
          have notSet : v1.getLsbD 0 ≠ true := by simpa [small1] using bit1
          cases h : v1.getLsbD 0 <;> simp_all
        have set : v2.getLsbD 0 = true := bit2.mpr small2
        rw [equal, set] at clear
        contradiction
    · have small2 : smallInt width i2 := either.resolve_left small1
      have set : v1.getLsbD 0 = true := bit1.mpr small1
      have clear : v2.getLsbD 0 = false := by
        have notSet : v2.getLsbD 0 ≠ true := by simpa [small2] using bit2
        cases h : v2.getLsbD 0 <;> simp_all
      rw [equal, clear] at set
      contradiction
  · intro equal
    subst i2
    have small : smallInt width i1 := either.elim id id
    have h1 := memoryRel_numberImp conf bigEndian next refs space store memory domain i1 w1
      ((.number i1, w2) :: vars) ⟨good, small, inv⟩
    have h2 := memoryRel_numberImp conf bigEndian next refs space store memory domain i1 w2 vars
      ⟨good, small, tail⟩
    have enc1 : v1 = smallnum i1 := WordLocW.word.inj (eq1.symm.trans h1)
    have enc2 : v2 = smallnum i1 := WordLocW.word.inj (eq2.symm.trans h2)
    exact enc1.trans enc2.symm

/-- Signed less-than-or-equal comparison of related small integers matches
source integer order. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Number_LESS_EQ"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_numberLessEq {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i1 i2 : Int) (w1 w2 : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain
      ((.number i1, w1) :: (.number i2, w2) :: vars) ∧
      smallInt width i1 ∧ smallInt width i2 ∧ goodDimindex width →
    ∃ v1 v2 : BitVec width, w1 = .word v1 ∧ w2 = .word v2 ∧
      (v1.sle v2 = true ↔ i1 ≤ i2) := by
  rintro ⟨inv, small1, small2, good⟩
  have first := memoryRel_numberImp conf bigEndian next refs space store memory domain i1 w1
    ((.number i2, w2) :: vars) ⟨good, small1, inv⟩
  have tail := memoryRel_tl conf bigEndian next refs space store memory domain
    (.number i1, w1) ((.number i2, w2) :: vars) inv
  have second := memoryRel_numberImp conf bigEndian next refs space store memory domain i2 w2 vars
    ⟨good, small2, tail⟩
  refine ⟨smallnum i1, smallnum i2, first, second, ?_⟩
  have bounds1 := smallnum_signedBounds good i1 small1
  have bounds2 := smallnum_signedBounds good i2 small2
  have pos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  rw [BitVec.sle_eq_decide, decide_eq_true_eq, smallnum_i2w, smallnum_i2w,
    BitVec.toInt_ofInt_eq_self pos bounds1.1 bounds1.2,
    BitVec.toInt_ofInt_eq_self pos bounds2.1 bounds2.2]
  omega

/-- A related small integer is negative exactly when the word sign bit is set. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Number_word_msb"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_numberWordMsb {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i : Int) (w : BitVec width) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain ((.number i, .word w) :: vars) ∧
      goodDimindex width ∧ smallInt width i → (w.msb = true ↔ i < 0) := by
  rintro ⟨inv, good, small⟩
  have word := WordLocW.word.inj (memoryRel_numberImp conf bigEndian next refs space store memory domain
    i (.word w) vars ⟨good, small, inv⟩)
  have bounds := smallnum_signedBounds good i small
  have pos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  rw [word, BitVec.msb_eq_toInt, decide_eq_true_eq, smallnum_i2w,
    BitVec.toInt_ofInt_eq_self pos bounds.1 bounds.2]
  omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
