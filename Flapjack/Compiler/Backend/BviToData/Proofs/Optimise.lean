module

public import Flapjack.Compiler.Backend.BviToData.Optimise
public import Flapjack.Compiler.Backend.BviToData.Proofs.CompileCorrect
public import Flapjack.Compiler.Backend.DataLive.Proofs.CompileCorrect
public import Flapjack.Compiler.Backend.DataSimp.Proofs.Correct
public import Flapjack.Compiler.Backend.Semantics.DataProps.Jump

@[expose] public section

/-! Composition of the established data optimization steps. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Liveness followed by sequence simplification preserves a stopped,
non-type-error result and changes only the four state fields permitted by
the source optimization theorem. This intermediate composition has no
separate HOL declaration. -/
theorem live_simp_correct {C F : Type} (program : DataLang.Prog) (state : State C F)
    (notType : (DataSem.evaluate program state).1 ≠ some (.err (.abort .typeError)))
    (stopped : (DataSem.evaluate program state).1 ≠ none) :
    ∃ localsSize stackMax safe peak,
      DataSem.evaluate (DataSimp.simp (DataLive.compile program .ln).1 .skip) state =
        ((DataSem.evaluate program state).1,
          { (DataSem.evaluate program state).2 with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }) := by
  obtain ⟨localsSize, stackMax, safe, peak, correct⟩ := DataLive.compile_correct program state notType stopped
  exact ⟨localsSize, stackMax, safe, peak, by simpa only [DataSimp.simp_correct] using correct⟩

/-- Resource-field changes preserve the terminal simulation obligations,
including the saved exception jump. This is composition infrastructure. -/
theorem correctOutcome_some_resources {C F : Type} (res : BviSem.BviResult)
    (initial final : State C F) (n next : Nat) (corr live names : List Nat)
    (env : List BvlSem.Value) (tail : Bool) (result : Result (List DataSem.Value) DataSem.Value)
    (ls localsSize stackMax : Option Nat) (safe : Bool) (peak : Nat)
    (outcome : correctOutcome res initial final n next corr live names env tail (some result) ls) :
    correctOutcome res initial
      { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }
      n next corr live names env tail (some result) ls := by
  rcases outcome with ⟨projected, returned, control, tailResult, jump⟩
  refine ⟨projected, returned, ?_, tailResult, ?_⟩
  · simpa using control
  · intro exception
    have old := jump exception
    have transported := DataSem.jumpExc_transport
      { final with stack := initial.stack, handler := initial.handler }
      { final with stack := initial.stack, handler := initial.handler, localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }
      { final with localsSize := ls } rfl rfl old
    simpa using transported

end Flapjack.Compiler.Backend.BviToData
