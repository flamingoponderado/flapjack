import Flapjack.Compiler.Backend.BvlToBvi.Proofs.InitialStateRel
import Flapjack.Compiler.Backend.Semantics.BvlSem.Semantics
import Flapjack.Compiler.Backend.Semantics.BviSem.Semantics
import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateClockShift

/-! Observable consequences of the BVL-to-BVI evaluation simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.SemanticPrimitivesHOL

/-- The compiled initial call cannot produce a fatal BVI error when the
source initial call never produces a type error. This uses clock extension to
compare a putative target error with a sufficiently long source simulation. -/
theorem compileProgFuel_noFatalError {C F : Type}
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
        (BackendProps.stateCc compileIncSource compiler) clock)).1 ≠ .err (.abort .typeError)) :
    ¬ ∃ clock error, (BviSem.evaluate [.call 0 (some targetStart) [] none] []
      (BviSem.initialState ffi (sptFromAList targetProgram)
        (BackendProps.stateCo compileIncSource oracle) compiler clock)).1 = .err error ∧
      error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event) := by
  rintro ⟨clock, error, fatalRun, notTimeout, notFfi⟩
  let source := BvlSem.evaluate [.call 0 (some start) []] []
    (BvlSem.initialState ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource compiler) (clock + 1))
  have sourceRun : BvlSem.evaluate [.call 0 (some start) []] []
      (BvlSem.initialState ffi (sptFromAList programs) oracle
        (BackendProps.stateCc compileIncSource compiler) (clock + 1)) = (source.1, source.2) := by
    exact Prod.mk.eta.symm
  have sourceNotType : source.1 ≠ .err (.abort .typeError) := noTypeError (clock + 1)
  obtain ⟨extra, relocate, targetState, targetRun, _⟩ :=
    compileProgFuelEvaluate fuel optFuel start counter (clock + 1) ffi programs oracle compiler
      targetStart targetNextName targetProgram source.1 source.2 compiled sourceRun distinct handlers
      oracleHandlers counterBound sourceNotType
  let target := BviSem.evaluate [.call 0 (some targetStart) [] none] []
    (BviSem.initialState ffi (sptFromAList targetProgram)
      (BackendProps.stateCo compileIncSource oracle) compiler clock)
  have targetPair : BviSem.evaluate [.call 0 (some targetStart) [] none] []
      (BviSem.initialState ffi (sptFromAList targetProgram)
        (BackendProps.stateCo compileIncSource oracle) compiler clock) = (.err error, target.2) := by
    exact Prod.ext fatalRun rfl
  have extended := BviProps.evaluate_addClock [.call 0 (some targetStart) [] none] []
    (BviSem.initialState ffi (sptFromAList targetProgram) (BackendProps.stateCo compileIncSource oracle) compiler clock)
    target.2 (.err error) (1 + extra) targetPair (by simpa using notTimeout)
  have sameResult : mapSimulationResult relocate (match source.1 with
      | .err (.raise value) => .val [value]
      | other => other) = .err error := by
    have eqRun := targetRun.symm.trans (by simpa [BviSem.initialState, Nat.add_assoc] using extended)
    exact congrArg Prod.fst eqRun
  cases h : source.1 with
  | val values => simp [h, mapSimulationResult] at sameResult
  | err e =>
    cases e with
    | raise value => simp [h, mapSimulationResult] at sameResult
    | abort reason =>
      cases reason with
      | typeError => exact sourceNotType h
      | timeoutError => simp [h, mapSimulationResult] at sameResult; exact notTimeout sameResult.symm
      | ffiError event => simp [h, mapSimulationResult] at sameResult; exact notFfi event sameResult.symm

/-- Under the compiler's well-formedness conditions, non-failure of the BVL
whole program entails non-failure of the compiled BVI whole program. -/
theorem compileProgFuel_semantics_ne_fail {C F : Type}
    (fuel optFuel start counter : Nat) (ffi : HolFfiState F)
    (programs : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Nat × C)) (compiler : BviSem.Compiler C)
    (targetStart targetNextName : Nat) (targetProgram : List (Nat × Nat × Bvi.Exp))
    (compiled : compileProgFuel fuel optFuel start counter programs = some (targetStart, targetProgram, targetNextName))
    (distinct : (programs.map Prod.fst).Nodup)
    (handlers : BvlHandle.Proofs.handleOk (programs.map (fun (_, _, body) => body)))
    (oracleHandlers : ∀ index, BvlHandle.Proofs.handleOk ((oracle index).2.map (fun (_, _, body) => body)))
    (counterBound : targetNextName ≤ (oracle 0).1.1)
    (nonfail : BvlSem.semantics ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource compiler) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList targetProgram)
      (BackendProps.stateCo compileIncSource oracle) compiler targetStart ≠ .fail := by
  apply BviSem.semantics_ne_fail_of_noFatalError
  apply compileProgFuel_noFatalError fuel optFuel start counter ffi programs oracle compiler
    targetStart targetNextName targetProgram compiled distinct handlers oracleHandlers counterBound
  exact BvlSem.noTypeError_of_semantics_ne_fail ffi (sptFromAList programs) oracle
    (BackendProps.stateCc compileIncSource compiler) start nonfail

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

/-- A terminating observation of the compiled program reflects back to the
source. Clock extension aligns the target run with a source simulation. -/
theorem compileProgFuel_reflect_terminatingObservation {C F : Type}
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
    (observation : BviSem.terminatingObservation ffi (sptFromAList targetProgram)
      (BackendProps.stateCo compileIncSource oracle) compiler targetStart behavior) :
    BvlSem.terminatingObservation ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource compiler) start behavior := by
  obtain ⟨clock, targetResult, targetState, outcome, targetRun, targetOutcome, behaviorEq⟩ := observation
  have targetNotTimeout : targetResult ≠ .err (.abort .timeoutError) := by
    intro h; subst targetResult; simp at targetOutcome
  let source := BvlSem.evaluate [.call 0 (some start) []] []
    (BvlSem.initialState ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource compiler) (clock + 1))
  have sourceRun : BvlSem.evaluate [.call 0 (some start) []] []
      (BvlSem.initialState ffi (sptFromAList programs) oracle
        (BackendProps.stateCc compileIncSource compiler) (clock + 1)) = (source.1, source.2) := Prod.mk.eta.symm
  have sourceNotType : source.1 ≠ .err (.abort .typeError) := noTypeError (clock + 1)
  obtain ⟨extra, relocate, simulatedState, simulatedRun, related⟩ :=
    compileProgFuelEvaluate fuel optFuel start counter (clock + 1) ffi programs oracle compiler
      targetStart targetNextName targetProgram source.1 source.2 compiled sourceRun distinct handlers
      oracleHandlers counterBound sourceNotType
  have extended := BviProps.evaluate_addClock [.call 0 (some targetStart) [] none] []
    (BviSem.initialState ffi (sptFromAList targetProgram) (BackendProps.stateCo compileIncSource oracle) compiler clock)
    targetState targetResult (1 + extra) targetRun targetNotTimeout
  have same : (mapSimulationResult relocate (match source.1 with
      | .err (.raise value) => .val [value]
      | other => other), simulatedState) =
      (targetResult, { targetState with clock := targetState.clock + (1 + extra) }) :=
    simulatedRun.symm.trans (by simpa [BviSem.initialState, Nat.add_assoc] using extended)
  have sameResult := congrArg Prod.fst same
  have sameEvents : source.2.ffi.ioEvents = targetState.ffi.ioEvents :=
    (congrArg (·.ioEvents) related.2.1).trans (congrArg (fun p => p.2.ffi.ioEvents) same)
  refine ⟨clock + 1, source.1, source.2, outcome, sourceRun, ?_, ?_⟩
  · cases h : source.1 with
    | val values =>
      simp [h, mapSimulationResult] at sameResult
      simpa [h, ← sameResult] using targetOutcome
    | err error =>
      cases error with
      | raise value =>
        simp [h, mapSimulationResult] at sameResult
        simpa [h, ← sameResult] using targetOutcome
      | abort reason =>
        cases reason with
        | typeError => exact False.elim (sourceNotType h)
        | timeoutError =>
          simp [h, mapSimulationResult] at sameResult
          exact False.elim (targetNotTimeout sameResult.symm)
        | ffiError event =>
          simp [h, mapSimulationResult] at sameResult
          simpa [h, ← sameResult] using targetOutcome
  · simpa [sameEvents] using behaviorEq

/-- If the source diverges, the compiled program also diverges. Equality of
their potentially infinite traces requires the clock-indexed prefix theorem. -/
theorem compileProgFuel_diverges {C F : Type}
    (fuel optFuel start counter : Nat) (ffi : HolFfiState F)
    (programs : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Nat × C)) (compiler : BviSem.Compiler C)
    (targetStart targetNextName : Nat) (targetProgram : List (Nat × Nat × Bvi.Exp))
    (compiled : compileProgFuel fuel optFuel start counter programs = some (targetStart, targetProgram, targetNextName))
    (distinct : (programs.map Prod.fst).Nodup)
    (handlers : BvlHandle.Proofs.handleOk (programs.map (fun (_, _, body) => body)))
    (oracleHandlers : ∀ index, BvlHandle.Proofs.handleOk ((oracle index).2.map (fun (_, _, body) => body)))
    (counterBound : targetNextName ≤ (oracle 0).1.1)
    (trace : HolLList HolIoEvent)
    (diverges : BvlSem.semantics ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource compiler) start = .diverge trace) :
    ∃ targetTrace, BviSem.semantics ffi (sptFromAList targetProgram)
      (BackendProps.stateCo compileIncSource oracle) compiler targetStart = .diverge targetTrace := by
  have nonfail : BvlSem.semantics ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource compiler) start ≠ .fail := by
    rw [diverges]; intro impossible; cases impossible
  have noTypeError := BvlSem.noTypeError_of_semantics_ne_fail ffi (sptFromAList programs)
    oracle (BackendProps.stateCc compileIncSource compiler) start nonfail
  have noFatal := compileProgFuel_noFatalError fuel optFuel start counter ffi programs oracle compiler
    targetStart targetNextName targetProgram compiled distinct handlers oracleHandlers counterBound noTypeError
  apply BviSem.semantics_diverges_of_no_observation _ _ _ _ _ noFatal
  intro behavior targetObserved
  have sourceObserved := compileProgFuel_reflect_terminatingObservation fuel optFuel start counter ffi programs oracle compiler
    targetStart targetNextName targetProgram compiled distinct handlers oracleHandlers counterBound noTypeError behavior targetObserved
  exact BvlSem.no_terminatingObservation_of_semantics_eq_diverge ffi (sptFromAList programs) oracle
    (BackendProps.stateCc compileIncSource compiler) start trace diverges behavior sourceObserved

/-- Executed BVL-to-BVI compilation preserves a terminating whole-program
behavior under the compiler's source well-formedness conditions. The
divergence case requires additional clock-indexed trace-prefix results. -/
theorem compileProgFuel_semantics_of_terminates {C F : Type}
    (fuel optFuel start counter : Nat) (ffi : HolFfiState F)
    (programs : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Nat × C)) (compiler : BviSem.Compiler C)
    (targetStart targetNextName : Nat) (targetProgram : List (Nat × Nat × Bvi.Exp))
    (compiled : compileProgFuel fuel optFuel start counter programs = some (targetStart, targetProgram, targetNextName))
    (distinct : (programs.map Prod.fst).Nodup)
    (handlers : BvlHandle.Proofs.handleOk (programs.map (fun (_, _, body) => body)))
    (oracleHandlers : ∀ index, BvlHandle.Proofs.handleOk ((oracle index).2.map (fun (_, _, body) => body)))
    (counterBound : targetNextName ≤ (oracle 0).1.1)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : BvlSem.semantics ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource compiler) start = .terminate outcome events) :
    BviSem.semantics ffi (sptFromAList targetProgram)
      (BackendProps.stateCo compileIncSource oracle) compiler targetStart =
    BvlSem.semantics ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource compiler) start := by
  have nonfail : BvlSem.semantics ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource compiler) start ≠ .fail := by
    rw [terminates]; intro impossible; cases impossible
  have noTypeError := BvlSem.noTypeError_of_semantics_ne_fail ffi (sptFromAList programs)
    oracle (BackendProps.stateCc compileIncSource compiler) start nonfail
  have noFatal := compileProgFuel_noFatalError fuel optFuel start counter ffi programs oracle compiler
    targetStart targetNextName targetProgram compiled distinct handlers oracleHandlers counterBound noTypeError
  have sourceObserved := BvlSem.terminatingObservation_of_semantics_eq_terminate ffi
    (sptFromAList programs) oracle (BackendProps.stateCc compileIncSource compiler) start outcome events terminates
  have targetObserved := compileProgFuel_terminatingObservation fuel optFuel start counter ffi programs oracle compiler
    targetStart targetNextName targetProgram compiled distinct handlers oracleHandlers counterBound noTypeError
    (.terminate outcome events) sourceObserved
  rw [terminates]
  exact BviSem.semantics_eq_of_terminatingObservation ffi (sptFromAList targetProgram)
    (BackendProps.stateCo compileIncSource oracle) compiler targetStart _ noFatal targetObserved

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
