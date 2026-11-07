import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
import Mathlib.Tactic.NormNum

/-! Space monotonicity of the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- A memory relation with a given allocation allowance also holds for any
smaller allowance. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_less_space"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_lessSpace {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space smaller : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain vars ∧ smaller ≤ space →
      memoryRel conf bigEndian next refs smaller store memory domain vars := by
  rintro ⟨⟨heap, limit, a, sp, sp1, gens, hstore, hword, hbound, hspace⟩, hsmaller⟩
  exact ⟨heap, limit, a, sp, sp1, gens, hstore, hword, hbound, Nat.le_trans hsmaller hspace⟩

/-- A valid memory relation remains valid with no requested allocation space. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_zero_space"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_zeroSpace {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain vars →
      memoryRel conf bigEndian next refs 0 store memory domain vars := by
  intro related
  exact memoryRel_lessSpace conf bigEndian next refs space 0 store memory domain vars
    ⟨related, Nat.zero_le _⟩

/-- The free-space portion of a word-level heap invariant fits its heap limit. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_ml_inv_SP_LIMIT"
  (words_as_type_indexed_bitvec)]
theorem wordMlInv_spLimit {width : Nat} [NeZero width] (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState) (limit next : Nat) (conf : Config)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (stack : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    wordMlInv (heap, bigEndian, a, sp, sp1, gens) limit next conf refs stack → sp ≤ limit := by
  rintro ⟨_, ⟨_, heapOk', _, unused, _⟩, _⟩
  have heapLengthEq := heapOk'.1
  have spaceBound := unused.2.1
  omega

/-- The active heap's free-space interval is represented by the target's
allocation and collection pointers, and its full length remains a valid
memory-relation allowance. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_space_max"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_spaceMax {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain vars →
    ∃ (nextFree triggerGc : BitVec width) (available : Nat),
      store.lookup .nextFree = some (.word nextFree) ∧ store.lookup .triggerGC = some (.word triggerGc) ∧
      triggerGc - nextFree = StackRemove.bytesInWord width * BitVec.ofNat width available ∧
      space ≤ available ∧ memoryRel conf bigEndian next refs available store memory domain vars ∧
      (goodDimindex width → (width / 8) * available < 2 ^ width) := by
  rintro ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, bound, spaceBound⟩
  have spLimit := wordMlInv_spLimit heap bigEndian a sp sp1 gens limit next conf refs vars wordInv
  obtain ⟨_, _, _, _, _, _, _, curr, other, currAligned, otherAligned, currStore, otherStore, nextStore,
    triggerStore, rest⟩ := heapMem
  refine ⟨curr + StackRemove.bytesInWord width * BitVec.ofNat width a,
    curr + StackRemove.bytesInWord width * BitVec.ofNat width (a + sp), sp,
    nextStore, triggerStore, ?_, spaceBound, ?_, ?_⟩
  · simp only [BitVec.ofNat_add, BitVec.mul_add]
    rw [← BitVec.add_assoc, BitVec.add_comm (curr + StackRemove.bytesInWord width * BitVec.ofNat width a),
      BitVec.add_sub_cancel]
  · refine ⟨heap, limit, a, sp, sp1, gens, ?_, wordInv, bound, Nat.le_refl sp⟩
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, curr, other, currAligned, otherAligned, currStore, otherStore, nextStore, triggerStore, rest⟩
  · intro good
    rcases good with h | h <;> subst width <;> norm_num at bound ⊢ <;> omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
