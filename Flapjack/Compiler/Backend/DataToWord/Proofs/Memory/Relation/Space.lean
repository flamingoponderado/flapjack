import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation

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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
