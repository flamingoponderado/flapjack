module

public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluatorSimulation

@[expose] public section

/-! Related call-entry states for the data evaluator. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Entering a tail call with identical arguments makes the local
environments equal and preserves the liveness state relation. This is
untagged auxiliary infrastructure. -/
theorem stateRel_tailEntry {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (size : Option Nat) (related : stateRel source target live) :
    stateRel (DataSem.callEnv args size (decClock source)) (DataSem.callEnv args size (decClock target)) .ln ∧
      (DataSem.callEnv args size (decClock source)).locals = (DataSem.callEnv args size (decClock target)).locals := by
  rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, _⟩
  refine ⟨?_, rfl⟩
  refine ⟨code, ?_, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, ?_⟩
  · simp [DataSem.callEnv, decClock, clock]
  · intro key member
    simp [sptMem, sptDomain, sptLookup] at member

/-- Tail-call entry preserves correspondence of exception jumps. -/
theorem exceptionRel_tailEntry {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (size : Option Nat) (related : stateRel source target live)
    (exception : exceptionRel source target) :
    exceptionRel (DataSem.callEnv args size (decClock source)) (DataSem.callEnv args size (decClock target)) := by
  apply exceptionRel_after source target _ _ .ln (stateRel_tailEntry source target live args size related).1 exception <;> rfl

/-- Same-program evaluation simulation for all entry states below a clock
bound. This packages the recursive induction hypothesis used at call sites. -/
def evaluatorSimulationBelow {C F : Type} (clock : Nat) : Prop :=
  ∀ (program : DataLang.Prog) (source target sourceNext : State C F)
    (result : Option (Result (List DataSem.Value) DataSem.Value)),
    source.clock < clock → stateRel source target .ln → source.locals = target.locals →
    exceptionRel source target → result ≠ some (.err (.abort .typeError)) →
    DataSem.evaluate program source = (result, sourceNext) →
    ∃ targetNext, DataSem.evaluate program target = (result, targetNext) ∧
      stateRel sourceNext targetNext .ln ∧ (result = none → sourceNext.locals = targetNext.locals)

end Flapjack.Compiler.Backend.DataLive
