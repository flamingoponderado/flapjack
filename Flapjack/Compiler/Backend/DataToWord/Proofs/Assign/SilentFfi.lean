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

/-- The full silent-FFI evaluation result. The HOL tag is pending review of
the state relation and compiler dependencies. The evaluator inherits the
real-model assumption recorded in SOUNDNESS item 8. -/
theorem evaluate_silentFfi_three {width : Nat} [NeZero width] {C F N : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
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
    readBytearrayWordHOL, writeBytearrayExact, callFFIHOL_empty_extCall]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
