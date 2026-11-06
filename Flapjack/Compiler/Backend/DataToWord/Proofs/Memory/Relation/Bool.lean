import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Unit

/-! Boolean values in the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined
open Flapjack.Compiler.Backend.BackendCommon

/-- True and its immediate word can be added to the full memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Boolv_T"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_boolTrue {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain vars ∧ goodDimindex width →
    memoryRel conf bigEndian next refs space store memory domain ((boolValue true, .word 18) :: vars) := by
  rintro ⟨⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, bound, spaceBound⟩, good⟩
  refine ⟨heap, limit, a, sp, sp1, gens, heapMem, ?_, bound, spaceBound⟩
  obtain ⟨roots, inv, addresses⟩ := wordInv
  have tagBound : 1 < 2 ^ width / 16 := by
    rcases good with h | h <;> subst width <;> decide
  refine ⟨.data (.word (blockNil 1)) :: roots, ?_, ?_⟩
  · simpa [boolValue, boolToTag, trueTag] using
      consThm_empty conf (vars.map Prod.fst) refs roots heap bigEndian a sp sp1 gens limit next 1 ⟨inv, tagBound⟩
  · apply List.Forall₂.cons
    · rcases good with h | h <;> subst width <;> simp [wordAddr, blockNil]
    · exact addresses

/-- False and its immediate word can be added to the full memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Boolv_F"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_boolFalse {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain vars ∧ goodDimindex width →
    memoryRel conf bigEndian next refs space store memory domain ((boolValue false, .word 2) :: vars) := by
  intro h
  simpa [boolValue, boolToTag, falseTag, unitValue] using
    memoryRel_unit conf bigEndian next refs space store memory domain vars h

/-- A Boolean can be added when its target location has the matching encoding. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Boolv"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_bool {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (b : Bool) (location : WordLocW width) :
    memoryRel conf bigEndian next refs space store memory domain vars ∧ goodDimindex width ∧
      (b = true → location = .word 18) ∧ (b = false → location = .word 2) →
    memoryRel conf bigEndian next refs space store memory domain ((boolValue b, location) :: vars) := by
  rintro ⟨inv, good, onTrue, onFalse⟩
  cases b with
  | false =>
      have eq := onFalse rfl
      subst location
      exact memoryRel_boolFalse conf bigEndian next refs space store memory domain vars ⟨inv, good⟩
  | true =>
      have eq := onTrue rfl
      subst location
      exact memoryRel_boolTrue conf bigEndian next refs space store memory domain vars ⟨inv, good⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
