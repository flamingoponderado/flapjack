import Flapjack.Compiler.Backend.BviToData.Optimise
import Flapjack.Compiler.Backend.DataLive.Proofs.CompileCorrect
import Flapjack.Compiler.Backend.DataSimp.Proofs.Correct

/-! Composition of the established data optimization steps. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Liveness followed by sequence simplification preserves a stopped,
non-type-error result and changes only the four state fields permitted by
the source optimization theorem. This intermediate composition has no
separate HOL declaration; the final data-space step remains to be proved. -/
theorem live_simp_correct {C F : Type} (program : DataLang.Prog) (state : State C F)
    (notType : (DataSem.evaluate program state).1 ≠ some (.err (.abort .typeError)))
    (stopped : (DataSem.evaluate program state).1 ≠ none) :
    ∃ localsSize stackMax safe peak,
      DataSem.evaluate (DataSimp.simp (DataLive.compile program .ln).1 .skip) state =
        ((DataSem.evaluate program state).1,
          { (DataSem.evaluate program state).2 with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }) := by
  obtain ⟨localsSize, stackMax, safe, peak, correct⟩ := DataLive.compile_correct program state notType stopped
  exact ⟨localsSize, stackMax, safe, peak, by simpa only [DataSimp.simp_correct] using correct⟩

end Flapjack.Compiler.Backend.BviToData
