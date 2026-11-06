import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StackOperations
import Flapjack.Compiler.Backend.DataToWord.Proofs.Numbers
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BitLemmas

/-! Small integers in the data-to-word abstract heap invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- A nonempty block occurring after adding a number already occurred in the
original stack or reference cells. This is Flapjack invariant infrastructure. -/
theorem allValues_numberBlock (i : Int) (refs : Spt (BvlSem.Ref Value))
    (stack : List Value) (stamp tag : Nat) (items : List Value)
    (member : allValues refs (.number i :: stack) (.block stamp tag items)) :
    allValues refs stack (.block stamp tag items) := by
  rcases member with a | b | c | d
  · exact Or.inl a
  · exact Or.inr (Or.inl b)
  · exact Or.inr (Or.inr (Or.inl c))
  · exact Or.inr (Or.inr (Or.inr (by simpa [valueListValues] using d)))

/-- A number adds no block, so replacing any stack prefix by it preserves uniqueness. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_Number"]
theorem blocksUnique_number (ws stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (next : Nat) (i : Int) :
    blocksUnique next (allValues refs (ws ++ stack)) →
    blocksUnique next (allValues refs (.number i :: stack)) := by
  intro unique stamp tag1 xs1 tag2 xs2 ⟨first, nonempty1, second, nonempty2⟩
  have liftBlock : ∀ tag items, allValues refs stack (.block stamp tag items) →
      allValues refs (ws ++ stack) (.block stamp tag items) := by
    intro tag items member
    rcases member with a | b | c | d
    · exact Or.inl a
    · exact Or.inr (Or.inl b)
    · exact Or.inr (Or.inr (Or.inl c))
    · apply Or.inr (Or.inr (Or.inr ?_))
      rw [valueListValues_append, List.mem_append]
      exact Or.inr d
  exact unique stamp tag1 xs1 tag2 xs2
    ⟨liftBlock tag1 xs1 (allValues_numberBlock i refs stack stamp tag1 xs1 first), nonempty1,
      liftBlock tag2 xs2 (allValues_numberBlock i refs stack stamp tag2 xs2 second), nonempty2⟩

/-- A small integer can be added to an abstract stack without allocating a heap cell. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "abs_ml_inv_Num"
  (words_as_type_indexed_bitvec)]
theorem absMlInv_num {width : Nat} [NeZero width] (conf : Config)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next : Nat) (i : Int) :
    absMlInv conf stack refs (roots, heap, bigEndian, a, sp, sp1, gens) limit next ∧ smallInt width i →
    absMlInv conf (.number i :: stack) refs
      (.data (.word (smallnum i)) :: roots, heap, bigEndian, a, sp, sp1, gens) limit next := by
  rintro ⟨⟨rootOk, heapOk', gc, unused, stackInv⟩, small⟩
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
    · simpa using blocksUnique_number [] stack refs next i unique
    · apply List.Forall₂.cons
      · exact (valueInv_number conf i refs _ f tf heap).mpr (by simp [small])
      · exact values
    · intro n ⟨reachable, domain⟩
      apply cells n
      refine ⟨?_, domain⟩
      obtain ⟨value, start, member, ref, path⟩ := reachable
      rcases List.mem_cons.mp member with same | inStack
      · subst value
        simp [getRefs] at ref
      · exact ⟨value, start, inStack, ref, path⟩

/-- The encoded small integer is unchanged by the immediate-value address mask.
This Flapjack helper establishes the bit-level step used by the memory proof. -/
theorem smallnum_mask {width : Nat} [NeZero width] (good : goodDimindex width) (i : Int) :
    (smallnum (width := width) i &&& ~~~(1 : BitVec width)) = smallnum i := by
  rw [smallnum_eq_inlined]
  rcases good with width32 | width64 <;> subst width
  all_goals split <;> apply bitAndNotOneEq <;> rw [bitLowToNat] <;>
    simp [BitVec.toNat_neg] <;> omega

/-- A small integer and its tagged word can be added to the full memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "IMP_memory_rel_Number"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem impMemoryRel_number {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (i : Int) :
    goodDimindex width ∧ smallInt width i ∧ memoryRel conf bigEndian next refs space store memory domain vars →
    memoryRel conf bigEndian next refs space store memory domain ((.number i, .word (smallnum i)) :: vars) := by
  rintro ⟨good, small, heap, limit, a, sp, sp1, gens, heapMem, wordInv, bound, spaceBound⟩
  refine ⟨heap, limit, a, sp, sp1, gens, heapMem, ?_, bound, spaceBound⟩
  obtain ⟨roots, inv, addresses⟩ := wordInv
  refine ⟨.data (.word (smallnum i)) :: roots, ?_, ?_⟩
  · exact absMlInv_num conf (vars.map Prod.fst) refs roots heap bigEndian a sp sp1 gens limit next i ⟨inv, small⟩
  · apply List.Forall₂.cons
    · simp only [wordAddr]
      rw [smallnum_mask good i]
    · exact addresses

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
