import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockStack
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockEquality
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.RefEquality

/-! Cases of pointer equality for the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- The block/block case of pointer equality, using the structural induction
hypothesis for each child of the first block. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_pointer_eq"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_pointerEq_blockBlock {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (ts1 tag1 ts2 tag2 : Nat) (vals1 vals2 : List Value) (location : WordLocW width) (b : Bool)
    (vars : List (Value × WordLocW width))
    (ih : ∀ child ∈ vals1, ∀ other loc result tail,
      memoryRel conf bigEndian next refs space store memory domain ((child, loc) :: (other, loc) :: tail) ∧
      goodDimindex width ∧ doEq refs child other = .val result →
      result = true)
    (h : memoryRel conf bigEndian next refs space store memory domain
        ((.block ts1 tag1 vals1, location) :: (.block ts2 tag2 vals2, location) :: vars) ∧
      goodDimindex width ∧ doEq refs (.block ts1 tag1 vals1) (.block ts2 tag2 vals2) = .val b) : b = true := by
  obtain ⟨inv, good, compare⟩ := h
  obtain ⟨w, locationEq, _⟩ := memoryRel_blockImp conf bigEndian next refs space store memory domain
    ts1 tag1 vals1 location ((.block ts2 tag2 vals2, location) :: vars) ⟨inv, good⟩
  subst location
  obtain ⟨tags, lengths⟩ := memoryRel_blocksSameWord conf bigEndian next refs space store memory domain
    ts1 tag1 ts2 tag2 vals1 vals2 w vars inv good
  subst tag2
  cases b with
  | true => rfl
  | false =>
    have listEq : doEqList refs vals1 vals2 = .val false := by
      by_cases clos1 : isClosure tag1 vals1 <;> by_cases clos2 : isClosure tag1 vals2 <;>
        simp [doEq, clos1, clos2, lengths] at compare
      exact compare
    obtain ⟨i, hi1, hi2, different⟩ := doEqList_falseElement refs vals1 vals2 ⟨listEq, lengths.symm⟩
    obtain ⟨w1, addr1, _, loc1, real1, _, inv1⟩ :=
      memoryRel_elAny conf bigEndian next refs space store memory domain ts1 tag1 vals1 (.word w)
        ((.block ts2 tag1 vals2, .word w) :: vars) i hi1 ⟨inv, good⟩
    have sameW1 : w = w1 := WordLocW.word.inj loc1
    subst w1
    let cell1 := memory (addr1 + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width i)
    have swapped : memoryRel conf bigEndian next refs space store memory domain
        ((.block ts2 tag1 vals2, .word w) :: (vals1[i], cell1) :: (.block ts1 tag1 vals1, .word w) :: vars) := by
      apply memoryRel_rearrange conf bigEndian next refs space store memory domain _ _ ?_ inv1
      intro pair member
      simp only [List.mem_cons] at member ⊢
      aesop
    obtain ⟨w2, addr2, _, loc2, real2, _, inv2⟩ :=
      memoryRel_elAny conf bigEndian next refs space store memory domain ts2 tag1 vals2 (.word w)
        ((vals1[i], cell1) :: (.block ts1 tag1 vals1, .word w) :: vars) i hi2 ⟨swapped, good⟩
    have sameW2 : w = w2 := WordLocW.word.inj loc2
    subst w2
    have sameAddr : addr1 = addr2 := Option.some.inj (real1.symm.trans real2)
    subst addr2
    have children : memoryRel conf bigEndian next refs space store memory domain
        ((vals1[i], cell1) :: (vals2[i], cell1) :: []) := by
      apply memoryRel_rearrange conf bigEndian next refs space store memory domain _ _ ?_ inv2
      intro pair member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      dsimp [cell1] at member ⊢
      aesop
    have impossible := ih vals1[i] (List.getElem_mem hi1) vals2[i] cell1 false [] ⟨children, good, different⟩
    contradiction

/-- The reference-pointer/reference-pointer case of pointer equality. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_pointer_eq"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_pointerEq_refRef {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (compare1 compare2 : Bool) (i1 i2 : Nat) (location : WordLocW width) (b : Bool)
    (vars : List (Value × WordLocW width))
    (h : memoryRel conf bigEndian next refs space store memory domain
        ((.refPtr compare1 i1, location) :: (.refPtr compare2 i2, location) :: vars) ∧
      goodDimindex width ∧ doEq refs (.refPtr compare1 i1) (.refPtr compare2 i2) = .val b) : b = true := by
  obtain ⟨inv, good, compare⟩ := h
  cases compare1 <;> cases compare2 <;> simp [doEq] at compare
  obtain ⟨w1, w2, eq1, eq2, same⟩ := memoryRel_refPtrEq conf bigEndian next refs space store memory domain
    i1 i2 location location vars ⟨inv, good⟩
  have sameWord : w1 = w2 := WordLocW.word.inj (eq1.symm.trans eq2)
  have sameIndex : i1 = i2 := same.mp sameWord
  subst i2
  cases lookup : sptLookup i1 refs with
  | none => simpa [lookup] using compare.symm
  | some cell =>
    cases cell <;> simp_all
    case byteArray flag bytes => cases flag <;> simp_all

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
