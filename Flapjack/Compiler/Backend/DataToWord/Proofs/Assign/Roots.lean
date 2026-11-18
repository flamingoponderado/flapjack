module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordMlInvGetVars

@[expose] public section

/-! Memory-relation preservation for corresponding local-variable reads. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace MemoryRelLookupVarPort

theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end MemoryRelLookupVarPort

/-- Adding successfully read corresponding locals preserves the memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "memory_rel_lookup_var_IMP"
  (fmap_as_finite_support_relation := [store, WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem memoryRel_lookupVars {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (be : Bool) (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (source : Spt Flapjack.Compiler.Backend.DataSem.Value) (target : WordSemStateFiniteExact width C F)
    (envs : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (names : List Nat)
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (words : List (WordLocW width))
    (premises : memoryRel conf be next refs space store memory domain
        (joinEnv source (sptToAList (sptInter target.locals (adjustSet source))) ++ envs) ∧
      DataSem.getVars names source = some values ∧
      WordSemStateFiniteExact.getVars (names.map adjustVar) target = some words) :
    memoryRel conf be next refs space store memory domain
      (values.zip words ++ joinEnv source (sptToAList (sptInter target.locals (adjustSet source))) ++ envs) := by
  obtain ⟨⟨heap, limit, a, sp, sp1, gens, heapMem, roots, bound, spaceBound⟩, reads, wordReads⟩ := premises
  exact ⟨heap, limit, a, sp, sp1, gens, heapMem,
    wordMlInv_getVars heap be a sp sp1 gens limit next conf refs source target names values words envs
      ⟨roots, reads, wordReads⟩, bound, spaceBound⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
