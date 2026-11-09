module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.PointerEquality

@[expose] public section

/-! Immediate-word comparisons for the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- The source's reordered shared-location consequence of pointer equality. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_ptr_eq"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_ptrEq {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (v1 v2 : Value) (location : WordLocW width) (b : Bool) (vars : List (Value × WordLocW width))
    (h : memoryRel conf bigEndian next refs space store memory domain ((v1, location) :: (v2, location) :: vars) ∧
      doEq refs v1 v2 = .val b ∧ goodDimindex width) : b = true :=
  memoryRel_pointerEq conf bigEndian next refs space store memory domain v1 v2 location b vars ⟨h.1, h.2.2, h.2.1⟩

/-- A related 64-bit value is represented by a pointer with its low bit set.
This is Flapjack infrastructure for the immediate-comparison proof. -/
theorem memoryRel_word64LowBit {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (word : BitVec 64) (location : WordLocW width) (vars : List (Value × WordLocW width))
    (inv : memoryRel conf bigEndian next refs space store memory domain ((.word64 word, location) :: vars)) :
    ∃ w : BitVec width, location = .word w ∧ w.getLsbD 0 = true := by
  obtain ⟨heap, limit, a, sp, sp1, gens, _, wordInv, _, _⟩ := inv
  obtain ⟨roots, absInv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := absInv
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stackInv
  cases roots with
  | nil => cases values
  | cons root rest =>
    cases values with
    | cons related _ =>
      cases addresses with
      | cons projected _ =>
        obtain ⟨ptr, rootEq, _⟩ := (valueInv_word64 conf word refs root f tf heap).mp related
        subst root
        exact ⟨getAddr conf ptr (.word 0), projected.symm, getAddr_lowBit conf ptr _⟩

/-- A related comparison reference has a pointer with its low bit set. This is
Flapjack infrastructure for the immediate-comparison proof. -/
theorem memoryRel_refTrueLowBit {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (index : Nat) (location : WordLocW width) (vars : List (Value × WordLocW width))
    (inv : memoryRel conf bigEndian next refs space store memory domain ((.refPtr true index, location) :: vars)) :
    ∃ w : BitVec width, location = .word w ∧ w.getLsbD 0 = true := by
  obtain ⟨heap, limit, a, sp, sp1, gens, _, wordInv, _, _⟩ := inv
  obtain ⟨roots, absInv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := absInv
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stackInv
  cases roots with
  | nil => cases values
  | cons root rest =>
    cases values with
    | cons related _ =>
      cases addresses with
      | cons projected _ =>
        obtain ⟨_, _, _, rootEq⟩ := (valueInv_refPtr_true conf index refs root f tf heap).mp related
        subst root
        exact ⟨getAddr conf (holFapply f index) (.word 0), projected.symm, getAddr_lowBit conf _ _⟩

/-- A related block encoded as an immediate has no fields. This is Flapjack
infrastructure for the immediate-comparison proof. -/
theorem memoryRel_blockLowBitEmpty {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp tag : Nat) (values : List Value) (w : BitVec width) (vars : List (Value × WordLocW width))
    (inv : memoryRel conf bigEndian next refs space store memory domain ((.block stamp tag values, .word w) :: vars))
    (good : goodDimindex width) (low : w.getLsbD 0 = false) : values = [] := by
  obtain ⟨w', eq, cases⟩ := memoryRel_blockImp conf bigEndian next refs space store memory domain
    stamp tag values (.word w) vars ⟨inv, good⟩
  have eqWord : w = w' := WordLocW.word.inj eq
  subst w'
  by_contra nonempty
  simp only [nonempty, ↓reduceIte] at cases
  obtain ⟨_, _, bit, _⟩ := cases
  rw [low] at bit
  contradiction

/-- Distinct target words for blocks compare false when either is immediate.
This is Flapjack infrastructure for the source immediate-comparison theorem. -/
theorem memoryRel_blocksDifferentImmediate {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (ts1 tag1 ts2 tag2 : Nat) (vals1 vals2 : List Value) (w1 w2 : BitVec width) (b : Bool)
    (vars : List (Value × WordLocW width))
    (inv : memoryRel conf bigEndian next refs space store memory domain
      ((.block ts1 tag1 vals1, .word w1) :: (.block ts2 tag2 vals2, .word w2) :: vars))
    (good : goodDimindex width) (different : w1 ≠ w2)
    (low : w1.getLsbD 0 = false ∨ w2.getLsbD 0 = false)
    (compare : doEq refs (.block ts1 tag1 vals1) (.block ts2 tag2 vals2) = .val b) : b = false := by
  have tail := memoryRel_tl conf bigEndian next refs space store memory domain
    (.block ts1 tag1 vals1, .word w1) ((.block ts2 tag2 vals2, .word w2) :: vars) inv
  have cases : (vals1 = [] ∨ vals2 = []) ∧ (vals1.length ≠ vals2.length ∨ tag1 ≠ tag2) := by
    rcases low with low1 | low2
    · refine ⟨Or.inl (memoryRel_blockLowBitEmpty conf bigEndian next refs space store memory domain
          ts1 tag1 vals1 w1 _ inv good low1), ?_⟩
      exact memoryRel_blocksDistinctImmediate conf bigEndian next refs space store memory domain
        ts1 tag1 ts2 tag2 vals1 vals2 w1 w2 vars ⟨inv, good, different, low1⟩
    · have swapped := memoryRel_swap conf bigEndian next refs space store memory domain
        (.block ts1 tag1 vals1, .word w1) (.block ts2 tag2 vals2, .word w2) vars inv
      have reverseDifferent := memoryRel_blocksDistinctImmediate conf bigEndian next refs space store memory domain
        ts2 tag2 ts1 tag1 vals2 vals1 w2 w1 vars ⟨swapped, good, Ne.symm different, low2⟩
      refine ⟨Or.inr (memoryRel_blockLowBitEmpty conf bigEndian next refs space store memory domain
          ts2 tag2 vals2 w2 vars tail good low2), ?_⟩
      rcases reverseDifferent with length | tag
      · exact Or.inl (Ne.symm length)
      · exact Or.inr (Ne.symm tag)
  have mismatch : ¬ (tag1 = tag2 ∧ vals1.length = vals2.length) := by
    rintro ⟨tagEq, lengthEq⟩
    rcases cases.2 with length | tag
    · exact length lengthEq
    · exact tag tagEq
  have noBoth : ¬ (isClosure tag1 vals1 ∧ isClosure tag2 vals2) := by
    rintro ⟨first, second⟩
    rcases cases.1 with empty | empty
    · simp [isClosure, empty] at first
    · simp [isClosure, empty] at second
  by_cases clos : isClosure tag1 vals1 ∨ isClosure tag2 vals2
  · simp [doEq, clos, noBoth] at compare
  · simpa [doEq, clos, mismatch] using compare.symm

/-- If at least one related word is immediate, machine-word equality agrees
with the result of source value equality. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_simple_eq"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_simpleEq {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (v1 v2 : Value) (loc1 loc2 : WordLocW width) (b : Bool) (vars : List (Value × WordLocW width))
    (h : memoryRel conf bigEndian next refs space store memory domain ((v1, loc1) :: (v2, loc2) :: vars) ∧
      doEq refs v1 v2 = .val b ∧ goodDimindex width) :
    ∃ w1 w2 : BitVec width, loc1 = .word w1 ∧ loc2 = .word w2 ∧
      (w1.getLsbD 0 = false ∨ w2.getLsbD 0 = false → ((w1 = w2) ↔ b = true)) := by
  obtain ⟨inv, compare, good⟩ := h
  cases v1 with
  | number i1 =>
    cases v2 with
    | number i2 =>
      have tail := memoryRel_tl conf bigEndian next refs space store memory domain
        (.number i1, loc1) ((.number i2, loc2) :: vars) inv
      obtain ⟨w1, eq1, bit1⟩ := memoryRel_anyNumberImp conf bigEndian next refs space store memory domain
        i1 loc1 ((.number i2, loc2) :: vars) ⟨good, inv⟩
      obtain ⟨w2, eq2, bit2⟩ := memoryRel_anyNumberImp conf bigEndian next refs space store memory domain
        i2 loc2 vars ⟨good, tail⟩
      refine ⟨w1, w2, eq1, eq2, ?_⟩
      intro low
      have small : smallInt width i1 ∨ smallInt width i2 := by
        rcases low with low1 | low2
        · left
          by_contra large
          have set := bit1.mpr large
          rw [low1] at set
          contradiction
        · right
          by_contra large
          have set := bit2.mpr large
          rw [low2] at set
          contradiction
      obtain ⟨u1, u2, locEq1, locEq2, wordEq⟩ := memoryRel_numberEq conf bigEndian next refs space store memory domain
        i1 i2 loc1 loc2 vars ⟨inv, small, good⟩
      have eqU1 : w1 = u1 := WordLocW.word.inj (eq1.symm.trans locEq1)
      have eqU2 : w2 = u2 := WordLocW.word.inj (eq2.symm.trans locEq2)
      subst u1
      subst u2
      have sourceEq : (i1 = i2) ↔ b = true := by
        cases b <;> simp_all [doEq]
      exact wordEq.trans sourceEq
    | word64 _ | block _ _ _ | codePtr _ | refPtr _ _ => simp [doEq] at compare
  | word64 x =>
    cases v2 with
    | word64 y =>
      have tail := memoryRel_tl conf bigEndian next refs space store memory domain
        (.word64 x, loc1) ((.word64 y, loc2) :: vars) inv
      obtain ⟨w1, eq1, bit1⟩ := memoryRel_word64LowBit conf bigEndian next refs space store memory domain
        x loc1 ((.word64 y, loc2) :: vars) inv
      obtain ⟨w2, eq2, bit2⟩ := memoryRel_word64LowBit conf bigEndian next refs space store memory domain y loc2 vars tail
      refine ⟨w1, w2, eq1, eq2, ?_⟩
      intro low
      rcases low with low1 | low2 <;> simp_all
    | number _ | block _ _ _ | codePtr _ | refPtr _ _ => simp [doEq] at compare
  | block ts1 tag1 vals1 =>
    cases v2 with
    | block ts2 tag2 vals2 =>
      have tail := memoryRel_tl conf bigEndian next refs space store memory domain
        (.block ts1 tag1 vals1, loc1) ((.block ts2 tag2 vals2, loc2) :: vars) inv
      obtain ⟨w1, eq1, _⟩ := memoryRel_blockImp conf bigEndian next refs space store memory domain
        ts1 tag1 vals1 loc1 ((.block ts2 tag2 vals2, loc2) :: vars) ⟨inv, good⟩
      obtain ⟨w2, eq2, _⟩ := memoryRel_blockImp conf bigEndian next refs space store memory domain
        ts2 tag2 vals2 loc2 vars ⟨tail, good⟩
      subst loc1
      subst loc2
      refine ⟨w1, w2, rfl, rfl, ?_⟩
      intro low
      by_cases equal : w1 = w2
      · subst w2
        have value := memoryRel_ptrEq conf bigEndian next refs space store memory domain
          (.block ts1 tag1 vals1) (.block ts2 tag2 vals2) (.word w1) b vars ⟨inv, compare, good⟩
        simp [value]
      · have value := memoryRel_blocksDifferentImmediate conf bigEndian next refs space store memory domain
          ts1 tag1 ts2 tag2 vals1 vals2 w1 w2 b vars inv good equal low compare
        simp [equal, value]
    | number _ | word64 _ | codePtr _ | refPtr _ _ => simp [doEq] at compare
  | codePtr _ => cases v2 <;> simp [doEq] at compare
  | refPtr flag1 i1 =>
    cases v2 with
    | refPtr flag2 i2 =>
      cases flag1 <;> cases flag2 <;> simp [doEq] at compare
      have tail := memoryRel_tl conf bigEndian next refs space store memory domain
        (.refPtr true i1, loc1) ((.refPtr true i2, loc2) :: vars) inv
      obtain ⟨w1, eq1, bit1⟩ := memoryRel_refTrueLowBit conf bigEndian next refs space store memory domain
        i1 loc1 ((.refPtr true i2, loc2) :: vars) inv
      obtain ⟨w2, eq2, bit2⟩ := memoryRel_refTrueLowBit conf bigEndian next refs space store memory domain i2 loc2 vars tail
      refine ⟨w1, w2, eq1, eq2, ?_⟩
      intro low
      rcases low with low1 | low2 <;> simp_all
    | number _ | word64 _ | block _ _ _ | codePtr _ => simp [doEq] at compare

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
