module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StackOperations

@[expose] public section

/-! Empty constructors and unit in the data-to-word memory invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Adding an empty block does not add a nonempty block to the traversal.
This is Flapjack invariant infrastructure. -/
theorem allValues_emptyBlock (tag0 : Nat) (refs : Spt (BvlSem.Ref Value))
    (stack : List Value) (stamp tag : Nat) (items : List Value) (nonempty : items ≠ [])
    (member : allValues refs (.block 0 tag0 [] :: stack) (.block stamp tag items)) :
    allValues refs stack (.block stamp tag items) := by
  rcases member with a | b | c | d
  · exact Or.inl a
  · exact Or.inr (Or.inl b)
  · exact Or.inr (Or.inr (Or.inl c))
  · exact Or.inr (Or.inr (Or.inr (by simpa [valueListValues, nonempty] using d)))

/-- An empty block preserves the uniqueness condition on nonempty blocks.
This is Flapjack invariant infrastructure. -/
theorem blocksUnique_emptyBlock (tag : Nat) (refs : Spt (BvlSem.Ref Value))
    (stack : List Value) (next : Nat) (unique : blocksUnique next (allValues refs stack)) :
    blocksUnique next (allValues refs (.block 0 tag [] :: stack)) := by
  intro stamp tag1 xs1 tag2 xs2 ⟨first, nonempty1, second, nonempty2⟩
  exact unique stamp tag1 xs1 tag2 xs2
    ⟨allValues_emptyBlock tag refs stack stamp tag1 xs1 nonempty1 first, nonempty1,
      allValues_emptyBlock tag refs stack stamp tag2 xs2 nonempty2 second, nonempty2⟩

/-- A nullary block with an encodable tag needs no heap allocation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "cons_thm_EMPTY"
  (words_as_type_indexed_bitvec)]
theorem consThm_empty {width : Nat} [NeZero width] (conf : Config)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next tag : Nat) :
    absMlInv conf stack refs (roots, heap, bigEndian, a, sp, sp1, gens) limit next ∧
      tag < 2 ^ width / 16 →
    absMlInv conf (.block 0 tag [] :: stack) refs
      (.data (.word (blockNil tag)) :: roots, heap, bigEndian, a, sp, sp1, gens) limit next := by
  rintro ⟨⟨rootOk, heapOk', gc, unused, stackInv⟩, tagBound⟩
  refine ⟨?_, heapOk', gc, unused, ?_⟩
  · intro ptr annotation member
    apply rootOk ptr annotation
    simpa using member
  · obtain ⟨f, tf, fInj, fDomain, tfInj, tfTimestamps, tfBound, endian, unique, values, cells⟩ := stackInv
    refine ⟨f, tf, fInj, fDomain, tfInj, ?_, tfBound, endian, ?_, ?_, ?_⟩
    · intro stamp domain
      obtain ⟨value, member, timestamp⟩ := tfTimestamps stamp domain
      refine ⟨value, ?_, timestamp⟩
      rcases member with inRef | inStack
      · exact Or.inl inRef
      · exact Or.inr (List.mem_cons_of_mem _ inStack)
    · exact blocksUnique_emptyBlock tag refs stack next unique
    · apply List.Forall₂.cons
      · exact (valueInv_emptyBlock conf 0 tag refs _ f tf heap).mpr ⟨rfl, tagBound, rfl⟩
      · exact values
    · intro n ⟨reachable, domain⟩
      apply cells n
      refine ⟨?_, domain⟩
      obtain ⟨value, start, member, ref, path⟩ := reachable
      rcases List.mem_cons.mp member with same | inStack
      · subst value
        simp [getRefs] at ref
      · exact ⟨value, start, inStack, ref, path⟩

/-- Unit can be prepended to the word-level ML invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_ml_inv_Unit"
  (words_as_type_indexed_bitvec)]
theorem wordMlInv_unit {width : Nat} [NeZero width] (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next : Nat) (conf : Config)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (ws : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    wordMlInv (heap, bigEndian, a, sp, sp1, gens) limit next conf refs ws ∧ goodDimindex width →
    wordMlInv (heap, bigEndian, a, sp, sp1, gens) limit next conf refs
      ((unitValue, .word 2) :: ws) := by
  rintro ⟨⟨roots, inv, addresses⟩, good⟩
  have bound : 0 < 2 ^ width / 16 := by
    rcases good with h | h <;> subst width <;> decide
  refine ⟨.data (.word (blockNil 0)) :: roots, ?_, ?_⟩
  · exact consThm_empty conf (ws.map Prod.fst) refs roots heap bigEndian a sp sp1 gens limit next 0 ⟨inv, bound⟩
  · apply List.Forall₂.cons
    · rcases good with h | h <;> subst width <;> simp [wordAddr, blockNil]
    · exact addresses

/-- Unit and its tagged word can be added to the full memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Unit"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_unit {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain vars ∧ goodDimindex width →
    memoryRel conf bigEndian next refs space store memory domain ((unitValue, .word 2) :: vars) := by
  rintro ⟨⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, bound, spaceBound⟩, good⟩
  exact ⟨heap, limit, a, sp, sp1, gens, heapMem,
    wordMlInv_unit heap bigEndian a sp sp1 gens limit next conf refs vars ⟨wordInv, good⟩, bound, spaceBound⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
