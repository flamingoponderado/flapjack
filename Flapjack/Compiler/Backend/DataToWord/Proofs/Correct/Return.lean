import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ReturnRoots
import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

/-! The return case of the production-backed 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- When the source return reads its values, compiled return produces a
same-length word list at the saved return location. The flushed states remain
related with the returned pairs as additional memory roots. -/
theorem return64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (names : List Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVars names source.locals = some values) :
    ∃ words,
      values.length = words.length ∧
      DataSem.evaluate (.return names) source = (some (.val values), DataSem.flushState false source) ∧
      WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.return names)).1 target =
        (some (.result (.loc l1 l2) words), WordSemStateFiniteExact.flushState false target) ∧
      BackendProps.optionLe (WordSemStateFiniteExact.flushState false target).stackMax (DataSem.flushState false source).stackMax ∧
      stateRel64 conf l1 l2 (DataSem.flushState false source) (WordSemStateFiniteExact.flushState false target)
        (some (values.zip words)) locs := by
  obtain ⟨words, wordRun, size⟩ := stateRel64_getVars conf l1 l2 source target none locs related names values sourceRun
  have zero : WordSemStateFiniteExact.getVar 0 target = some (.loc l1 l2) := related.2.2.2.2.2.2.2.2.2.2.1 rfl
  have withRoots := stateRel64_returnRoots conf l1 l2 source target locs related names values words sourceRun wordRun
  refine ⟨words, size, ?_, ?_, related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
  · simp [DataSem.evaluate, sourceRun]
  · simp [compileControl64, compileControl?, WordSemStateFiniteExact.evaluate, zero, wordRun]
  · exact stateRel64_flushReturn conf l1 l2 source target locs (values.zip words) withRoots

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
