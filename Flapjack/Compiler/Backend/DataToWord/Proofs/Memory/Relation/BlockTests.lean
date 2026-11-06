import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeader
import Mathlib.Tactic.NormNum

/-! Constructor-tag tests in the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- A related constructor's tag fits the target word's tag range. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_tag_limit"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_tagLimit {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp tag : Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value) (location : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain ((.block stamp tag values, location) :: vars) ∧
      goodDimindex width → tag < 2 ^ width / 16 := by
  intro h
  obtain ⟨w, _, cases⟩ := memoryRel_blockImp conf bigEndian next refs space store memory domain stamp tag values location vars h
  by_cases empty : values = []
  · simp only [empty, ↓reduceIte] at cases
    exact cases.2.2.1
  · simp only [empty, ↓reduceIte] at cases
    obtain ⟨_, _, _, _, _, _, _, _, _, _, encoded, _⟩ := cases
    unfold encodeHeader at encoded
    split at encoded
    next condition => omega
    next condition => contradiction

/-- A rejected nonzero header cannot describe a related constructor. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_test_none_eq"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_testNoneEq {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp tag n len : Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value) (location : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    (encodeHeader conf (4 * n) len : Option (BitVec width)) = none ∧
      memoryRel conf bigEndian next refs space store memory domain ((.block stamp tag values, location) :: vars) ∧
      len ≠ 0 ∧ goodDimindex width → ¬ (tag = n ∧ values.length = len) := by
  rintro ⟨missing, inv, nonzero, good⟩ ⟨rfl, lengthEq⟩
  have notEmpty : values ≠ [] := by
    intro empty
    subst values
    simp at lengthEq
    exact nonzero lengthEq.symm
  obtain ⟨w, _, cases⟩ := memoryRel_blockImp conf bigEndian next refs space store memory domain stamp tag values location vars ⟨inv, good⟩
  simp only [notEmpty, ↓reduceIte] at cases
  obtain ⟨_, header, _, _, _, _, _, _, _, _, encoded, _⟩ := cases
  rw [lengthEq, missing] at encoded
  cases encoded

/-- Immediate nullary block encodings have a clear pointer bit. This is
Flapjack bit-vector infrastructure. -/
theorem nilEncoding_lowBit {width : Nat} [NeZero width] (good : goodDimindex width) (n : Nat) :
    (BitVec.ofNat width (16 * n + 2)).getLsbD 0 = false := by
  have h := (blockNil_mask good n).2
  rw [(blockNil_mask good n).1] at h
  simpa [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.mul_comm] using h

/-- Nullary block tags are injectively encoded within the source tag bound.
This is Flapjack arithmetic infrastructure. -/
theorem nilEncoding_injective {width : Nat} [NeZero width] (good : goodDimindex width) (tag n : Nat)
    (ht : tag < 2 ^ width / 16) (hn : n < 2 ^ width / 16)
    (eq : (BitVec.ofNat width tag * 16 + 2) = BitVec.ofNat width (16 * n + 2)) : tag = n := by
  have htBound : 16 * tag + 2 < 2 ^ width := by
    rcases good with h | h <;> subst width <;> norm_num at ht ⊢ <;> omega
  have hnBound : 16 * n + 2 < 2 ^ width := by
    rcases good with h | h <;> subst width <;> norm_num at hn ⊢ <;> omega
  have wordEq : BitVec.ofNat width (16 * tag + 2) = BitVec.ofNat width (16 * n + 2) := by
    simpa [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.mul_comm] using eq
  have natEq := congrArg BitVec.toNat wordEq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htBound, Nat.mod_eq_of_lt hnBound] at natEq
  omega

/-- Testing the immediate nullary encoding succeeds exactly for the matching
empty constructor. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_test_nil_eq"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_testNilEq {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp tag n : Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value) (location : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain ((.block stamp tag values, location) :: vars) ∧
      n < 2 ^ width / 16 ∧ goodDimindex width →
    ∃ v : BitVec width, location = .word v ∧ (v = BitVec.ofNat width (16 * n + 2) ↔ tag = n ∧ values = []) := by
  rintro ⟨inv, nBound, good⟩
  obtain ⟨v, locationEq, cases⟩ := memoryRel_blockImp conf bigEndian next refs space store memory domain
    stamp tag values location vars ⟨inv, good⟩
  refine ⟨v, locationEq, ?_⟩
  by_cases empty : values = []
  · simp only [empty, ↓reduceIte] at cases
    obtain ⟨encoded, _, tagBound, _⟩ := cases
    constructor
    · intro equal
      exact ⟨nilEncoding_injective good tag n tagBound nBound (encoded.symm.trans equal), empty⟩
    · rintro ⟨rfl, _⟩
      simpa [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.mul_comm] using encoded
  · simp only [empty, ↓reduceIte] at cases
    obtain ⟨_, _, low, _⟩ := cases
    constructor
    · intro equal
      have clear := nilEncoding_lowBit (width := width) good n
      rw [← equal, low] at clear
      contradiction
    · rintro ⟨_, impossible⟩
      exact False.elim (empty impossible)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
