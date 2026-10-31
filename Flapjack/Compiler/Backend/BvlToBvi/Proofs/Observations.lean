import Flapjack.Compiler.Backend.BvlToBvi.Proofs.InitialStateRel
import Flapjack.Compiler.Backend.Semantics.BvlSem.Semantics
import Flapjack.Compiler.Backend.Semantics.BviSem.Semantics

/-! Observable consequences of the BVL-to-BVI evaluation simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.SemanticPrimitivesHOL

/-- Every terminating source observation is also a target observation, if
the source never produces a type error. This is a forward simulation result;
whole-program behavior equality also requires clock and trace arguments. -/
theorem compileProgFuel_terminatingObservation {C F : Type}
    (fuel optFuel start counter : Nat) (ffi : HolFfiState F)
    (programs : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Nat × C)) (compiler : BviSem.Compiler C)
    (targetStart targetNextName : Nat) (targetProgram : List (Nat × Nat × Bvi.Exp))
    (compiled : compileProgFuel fuel optFuel start counter programs = some (targetStart, targetProgram, targetNextName))
    (distinct : (programs.map Prod.fst).Nodup)
    (handlers : BvlHandle.Proofs.handleOk (programs.map (fun (_, _, body) => body)))
    (oracleHandlers : ∀ index, BvlHandle.Proofs.handleOk ((oracle index).2.map (fun (_, _, body) => body)))
    (counterBound : targetNextName ≤ (oracle 0).1.1)
    (noTypeError : ∀ clock, (BvlSem.evaluate [.call 0 (some start) []] []
      (BvlSem.initialState ffi (sptFromAList programs) oracle
        (BackendProps.stateCc compileIncSource compiler) clock)).1 ≠ .err (.abort .typeError))
    (behavior : HolBehaviour)
    (observation : BvlSem.terminatingObservation ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource compiler) start behavior) :
    BviSem.terminatingObservation ffi (sptFromAList targetProgram)
      (BackendProps.stateCo compileIncSource oracle) compiler targetStart behavior := by
  obtain ⟨clock, result, state, outcome, run, resultOutcome, behaviorEq⟩ := observation
  have run' : BvlSem.evaluate [.call 0 (some start) []] []
      (BvlSem.initialState ffi (sptFromAList programs) oracle
        (BackendProps.stateCc compileIncSource compiler) clock) = (result, state) := run
  have notTypeError : result ≠ .err (.abort .typeError) := by
    simpa [run'] using noTypeError clock
  obtain ⟨extra, relocate, targetState, targetRun, related⟩ :=
    compileProgFuelEvaluate fuel optFuel start counter clock ffi programs oracle compiler
      targetStart targetNextName targetProgram result state compiled run' distinct handlers
      oracleHandlers counterBound notTypeError
  have ffiEq : state.ffi.ioEvents = targetState.ffi.ioEvents := congrArg (·.ioEvents) related.2.1
  refine ⟨clock + extra, _, targetState, outcome, targetRun, ?_, ?_⟩
  · cases result with
    | val values => simpa [mapSimulationResult] using resultOutcome
    | err error =>
      cases error with
      | raise value => simpa [mapSimulationResult] using resultOutcome
      | abort reason => cases reason <;> simp_all [mapSimulationResult]
  · simpa [ffiEq] using behaviorEq

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
