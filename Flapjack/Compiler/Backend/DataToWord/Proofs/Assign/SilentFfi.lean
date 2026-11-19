module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Heap
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutOdd
public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.FfiBridge

@[expose] public section

/-! Evaluation of the silent FFI sequence emitted for assignments. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

namespace reviewedEvaluate_silentFfi_threeMap
/-- Canonical roundtrip for the target state used by this HOL port. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end reviewedEvaluate_silentFfi_threeMap

/-- The full silent-FFI evaluation result. The evaluator inherits the
real-model assumption recorded in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_SilentFFI_3"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_silentFfi_three {width : Nat} [NeZero width] {C F N : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : Spt N) (env : Spt (WordLocW width))
    (premises : conf.callEmptyFfi = true ∧ stateRel conf l1 l2 source target none locs ∧
      wordSemCutEnv (adjustSets names) target.locals = some env) :
    WordSemStateFiniteExact.evaluate (silentFfi conf 3 (adjustSets names)) target =
      (none, { target with locals := env, fpRegs := HolFiniteMapExact.empty,
                           memory := target.memory, ffi := target.ffi }) := by
  obtain ⟨enabled, related, cut⟩ := premises
  obtain ⟨nf, curr, len, hnf, hcurr, hlen⟩ := stateRel_lookupHeap conf l1 l2 source target locs related
  simp [silentFfi, enabled, wordListSeq, WordSemStateFiniteExact.evaluate,
    WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
    WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
    WordSemStateFiniteExact.fixClock, theWords, wordOpHOL, wordOp,
    sptLookup_sptInsert_same, sptLookup_sptInsert_ne,
    hnf, hcurr, hlen, cut, cutEnv_adjustSets_insertOdd,
    readBytearrayWordHOL, readBytearrayGenericHOL, writeBytearrayExact, callFFIHOL_empty_extCall]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
