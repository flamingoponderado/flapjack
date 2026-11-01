import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeaderInjective
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange

/-! Shared-pointer constructor facts for the source equality proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Related blocks with the same target word have the same tag and length.
This Flapjack helper isolates a step in the recursive source pointer-equality
proof; it is not the full HOL pointer-equality theorem. -/
theorem memoryRel_blocksSameWord {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (ts1 tag1 ts2 tag2 : Nat) (vals1 vals2 : List Flapjack.Compiler.Backend.DataSem.Value) (w : BitVec width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (inv : memoryRel conf bigEndian next refs space store memory domain
      ((.block ts1 tag1 vals1, .word w) :: (.block ts2 tag2 vals2, .word w) :: vars))
    (good : goodDimindex width) : tag1 = tag2 ∧ vals1.length = vals2.length := by
  have config : conf.lenSize + 2 < width := by
    obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, _, _, _⟩ := inv
    have bound := heapMem.2.2.2.2.1
    omega
  have tail := memoryRel_tl conf bigEndian next refs space store memory domain
    (.block ts1 tag1 vals1, .word w) ((.block ts2 tag2 vals2, .word w) :: vars) inv
  obtain ⟨w1, heq1, case1⟩ := memoryRel_blockImp conf bigEndian next refs space store memory domain
    ts1 tag1 vals1 (.word w) ((.block ts2 tag2 vals2, .word w) :: vars) ⟨inv, good⟩
  obtain ⟨w2, heq2, case2⟩ := memoryRel_blockImp conf bigEndian next refs space store memory domain
    ts2 tag2 vals2 (.word w) vars ⟨tail, good⟩
  have e1 : w = w1 := WordLocW.word.inj heq1
  have e2 : w = w2 := WordLocW.word.inj heq2
  subst w1
  subst w2
  by_cases empty1 : vals1 = []
  · simp only [empty1, ↓reduceIte] at case1
    obtain ⟨encoding1, bit1, bound1, _⟩ := case1
    by_cases empty2 : vals2 = []
    · simp only [empty2, ↓reduceIte] at case2
      obtain ⟨encoding2, _, bound2, _⟩ := case2
      have eqTag : tag1 = tag2 := by
        apply nilEncoding_injective good tag1 tag2 bound1 bound2
        simpa [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.mul_comm] using encoding1.symm.trans encoding2
      simp [eqTag, empty1, empty2]
    · simp only [empty2, ↓reduceIte] at case2
      obtain ⟨_, _, bit2, _⟩ := case2
      rw [bit1] at bit2
      contradiction
  · simp only [empty1, ↓reduceIte] at case1
    obtain ⟨addr1, header1, bit1, _, _, addrEq1, memEq1, _, _, _, enc1, _⟩ := case1
    by_cases empty2 : vals2 = []
    · simp only [empty2, ↓reduceIte] at case2
      obtain ⟨_, bit2, _, _⟩ := case2
      rw [bit1] at bit2
      contradiction
    · simp only [empty2, ↓reduceIte] at case2
      obtain ⟨addr2, header2, _, _, _, addrEq2, memEq2, _, _, _, enc2, _⟩ := case2
      have equalAddr : addr1 = addr2 := Option.some.inj (addrEq1.symm.trans addrEq2)
      subst addr2
      have equalHeader : header1 = header2 := WordLocW.word.inj (memEq1.symm.trans memEq2)
      have parts := (encodeHeader_eq conf (4 * tag1) vals1.length (4 * tag2) vals2.length header1 header2
        ⟨enc1, enc2, config⟩).mp equalHeader
      exact ⟨by omega, parts.2⟩

/-- Distinct block words cannot have the same tag and length when the first
word is an immediate constructor. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Block_Block_small_eq"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_blocksDistinctImmediate {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (ts1 tag1 ts2 tag2 : Nat) (vals1 vals2 : List Flapjack.Compiler.Backend.DataSem.Value)
    (w1 w2 : BitVec width) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain
      ((.block ts1 tag1 vals1, .word w1) :: (.block ts2 tag2 vals2, .word w2) :: vars) ∧
      goodDimindex width ∧ w1 ≠ w2 ∧ w1.getLsbD 0 = false →
    vals1.length ≠ vals2.length ∨ tag1 ≠ tag2 := by
  rintro ⟨inv, good, different, low⟩
  by_contra no
  have lenEq : vals1.length = vals2.length := by
    by_contra h
    exact no (Or.inl h)
  have tagEq : tag1 = tag2 := by
    by_contra h
    exact no (Or.inr h)
  have tail := memoryRel_tl conf bigEndian next refs space store memory domain
    (.block ts1 tag1 vals1, .word w1) ((.block ts2 tag2 vals2, .word w2) :: vars) inv
  obtain ⟨w1', eq1, case1⟩ := memoryRel_blockImp conf bigEndian next refs space store memory domain
    ts1 tag1 vals1 (.word w1) ((.block ts2 tag2 vals2, .word w2) :: vars) ⟨inv, good⟩
  have w1Eq : w1 = w1' := WordLocW.word.inj eq1
  subst w1'
  have empty1 : vals1 = [] := by
    by_contra nonempty
    simp only [nonempty, ↓reduceIte] at case1
    obtain ⟨_, _, set, _⟩ := case1
    rw [low] at set
    contradiction
  have empty2 : vals2 = [] := by
    have lenZero : vals2.length = 0 := by simpa [empty1] using lenEq.symm
    exact List.eq_nil_of_length_eq_zero lenZero
  simp only [empty1, ↓reduceIte] at case1
  obtain ⟨w2', eq2, case2⟩ := memoryRel_blockImp conf bigEndian next refs space store memory domain
    ts2 tag2 vals2 (.word w2) vars ⟨tail, good⟩
  have w2Eq : w2 = w2' := WordLocW.word.inj eq2
  subst w2'
  simp only [empty2, ↓reduceIte] at case2
  apply different
  rw [case1.1, case2.1, tagEq]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
