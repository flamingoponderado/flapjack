import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.Reference

/-! Equality of comparison references in the abstract heap invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Related pointer-comparison references have equal abstract roots exactly
when their source reference indices are equal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ref_eq_thm"
  (words_as_type_indexed_bitvec)]
theorem refEqThm {width : Nat} [NeZero width] (conf : Config)
    (p1 p2 : Nat) (stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (r1 r2 : HeapAddress (WordLocW width)) (roots : List (HeapAddress (WordLocW width)))
    (heap : ValueHeap width) (bigEndian : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next : Nat) :
    absMlInv conf (.refPtr true p1 :: .refPtr true p2 :: stack) refs
      (r1 :: r2 :: roots, heap, bigEndian, a, sp, sp1, gens) limit next →
    (p1 = p2 ↔ r1 = r2) ∧ ∃ q1 q2, r1 = .pointer q1 (.word 0) ∧ r2 = .pointer q2 (.word 0) := by
  intro inv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, inj, _, _, _, _, _, _, values, _⟩ := stackInv
  cases values with
  | cons v1 rest =>
    cases rest with
    | cons v2 _ =>
      obtain ⟨d1, _, _, pos1⟩ := (valueInv_refPtr_true conf p1 refs r1 f tf heap).mp v1
      obtain ⟨d2, _, _, pos2⟩ := (valueInv_refPtr_true conf p2 refs r2 f tf heap).mp v2
      subst r1
      subst r2
      constructor
      · constructor
        · intro equal
          subst p2
          rfl
        · intro equal
          apply inj.2 p1 p2 ⟨d1, d2⟩
          exact (HeapAddress.pointer.inj equal).1
      · exact ⟨holFapply f p1, holFapply f p2, rfl, rfl⟩

/-- A reference to a byte array has the same abstract address for either
comparison flag. This is Flapjack infrastructure for byte-array equality. -/
theorem valueInv_byteRefAddress {width : Nat} [NeZero width] (conf : Config) (bit : Bool) (index : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
    (compare : Bool) (bytes : List (BitVec 8))
    (found : sptLookup index refs = some (.byteArray compare bytes))
    (related : valueInv conf (.refPtr bit index) refs (address, f, tf, heap)) :
    address = .pointer (holFapply f index) (.word 0) := by
  rcases (valueInv_refPtr conf bit index refs address f tf heap).mp related with ordinary | thunk | inlined
  · simpa [found, refPtrAnnot] using ordinary.2.2.2
  · obtain ⟨_, _, _, thunkFound, _⟩ := thunk
    rw [found] at thunkFound
    cases thunkFound
  · obtain ⟨_, thunkFound, _⟩ := inlined
    rw [found] at thunkFound
    cases thunkFound

/-- Two references to the same byte array have equal target words. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_RefPtr_EQ_IMP"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_refPtrEqImp {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (b1 b2 : Bool) (index : Nat) (w1 w2 : BitVec width) (compare : Bool) (bytes : List (BitVec 8))
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain
      ((.refPtr b1 index, .word w1) :: (.refPtr b2 index, .word w2) :: vars) ∧
      goodDimindex width ∧ sptLookup index refs = some (.byteArray compare bytes) → w1 = w2 := by
  rintro ⟨⟨heap, limit, a, sp, sp1, gens, _, wordInv, _, _⟩, _, found⟩
  obtain ⟨roots, inv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stackInv
  cases roots with
  | nil => cases values
  | cons root1 rest =>
    cases rest with
    | nil => cases values with | cons _ tail => cases tail
    | cons root2 rest =>
      cases values with
      | cons first more =>
        cases more with
        | cons second _ =>
          cases addresses with
          | cons addr1 more =>
            cases more with
            | cons addr2 _ =>
              have eq1 := valueInv_byteRefAddress conf b1 index refs root1 f tf heap compare bytes found first
              have eq2 := valueInv_byteRefAddress conf b2 index refs root2 f tf heap compare bytes found second
              rw [eq1] at addr1
              rw [eq2] at addr2
              exact WordLocW.word.inj (addr1.symm.trans addr2)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
