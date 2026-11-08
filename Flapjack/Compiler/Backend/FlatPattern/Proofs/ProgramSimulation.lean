import Flapjack.Compiler.Backend.FlatPattern.Proofs.ClockedInduction
import Flapjack.Compiler.Backend.FlatProps.EvalSim

/-! Program-level simulation for the flat pattern compiler. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend

/-- Related installation configurations give a program evaluation simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_decs_eval_sim"]
theorem compileDecs_evalSim {C F : Type} (cfg cfg2 : Config) (ffi : HolFfiState F)
    (source target : List FlatLang.Exp) (sourceConfig targetConfig : FlatSem.InstallConfig C)
    (configs : installConfRel cfg sourceConfig targetConfig) :
    FlatProps.evalSim ffi source target sourceConfig targetConfig
      (fun decs decs' => decs.map (compileDec cfg2) = decs') false := by
  intro clock sourceResult sourceState run safe programs
  have sourceSafe : sourceResult ≠ some (.abort .typeError) := by simpa using safe
  subst target
  have states := stateRel_initial cfg ffi clock sourceConfig targetConfig configs
  obtain ⟨targetState, targetResult, targetRun, results, finalStates⟩ :=
    (compileExps_evaluate cfg).2 _ source _ sourceState cfg2 _ sourceResult ⟨run, rfl, states, sourceSafe⟩
  refine ⟨0, targetResult, targetState, by simpa using targetRun, finalStates.2.2.1.symm, ?_, ?_, ?_⟩
  · intro isNone
    subst sourceResult
    cases targetResult <;> simp_all [optionRel]
  · intro value isRaise
    subst sourceResult
    cases targetResult with
    | none => simp [optionRel] at results
    | some error =>
      cases error <;> simp_all [optionRel, SemanticPrimitivesProps.excRel]
  · intro abort isAbort
    subst sourceResult
    cases targetResult with
    | none => simp [optionRel] at results
    | some error =>
      cases error <;> simp_all [optionRel, SemanticPrimitivesProps.excRel]

/-- The observable termination class of a declaration result. -/
def outcomeObservation (result : Option (SemanticPrimitivesHOL.ErrorResult FlatSem.Value)) (outcome : HolOutcome) : Prop :=
  match result, outcome with
  | some (.abort (.ffiError event)), outcome => outcome = HolOutcome.ffiOutcome event
  | some (.abort _), _ => False
  | _, outcome => outcome = HolOutcome.success

/-- Related declaration outcomes have the same observable termination class. -/
theorem outcomeRel_observation (source target : Option (SemanticPrimitivesHOL.ErrorResult FlatSem.Value))
    (related : optionRel (SemanticPrimitivesProps.excRel ValueRel) source target) (outcome : HolOutcome) :
    outcomeObservation source outcome ↔ outcomeObservation target outcome := by
  cases source with
  | none => cases target <;> simp_all [optionRel, outcomeObservation]
  | some sourceError =>
    cases target with
    | none => simp [optionRel] at related
    | some targetError =>
      cases sourceError <;> cases targetError <;>
        simp_all [optionRel, SemanticPrimitivesProps.excRel, outcomeObservation]

/-- A related optional outcome cannot introduce a type error. -/
theorem outcomeRel_noTypeError (source target : Option (SemanticPrimitivesHOL.ErrorResult FlatSem.Value))
    (related : optionRel (SemanticPrimitivesProps.excRel ValueRel) source target) (safe : source ≠ some (.abort .typeError)) :
    target ≠ some (.abort .typeError) := by
  intro bad
  subst target
  cases source with
  | none => simp [optionRel] at related
  | some error =>
    cases error <;> simp_all [optionRel, SemanticPrimitivesProps.excRel]

/-- Pattern compilation preserves the semantics of a non-failing program. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_decs_semantics"]
theorem compileDecs_semantics {C F : Type} (cfg cfg2 : Config) (ffi : HolFfiState F)
    (source : List FlatLang.Exp) (sourceConfig targetConfig : FlatSem.InstallConfig C)
    (configs : installConfRel cfg sourceConfig targetConfig)
    (notFail : FlatSem.semantics sourceConfig ffi source ≠ .fail) :
    FlatSem.semantics sourceConfig ffi source = FlatSem.semantics targetConfig ffi (source.map (compileDec cfg2)) := by
  classical
  have safe : ∀ clock, (FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source).2 ≠
      some (.abort .typeError) := by
    intro clock error
    have failure : FlatSem.semantics sourceConfig ffi source = .fail := by
      unfold FlatSem.semantics
      simp [show ∃ clock, (FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source).2 =
        some (.abort .typeError) from ⟨clock, error⟩]
    exact notFail failure
  have observations : ∀ clock,
      optionRel (SemanticPrimitivesProps.excRel ValueRel)
        (FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source).2
        (FlatSem.evaluateDecs (FlatSem.initialState ffi clock targetConfig) (source.map (compileDec cfg2))).2 ∧
      (FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source).1.ffi =
        (FlatSem.evaluateDecs (FlatSem.initialState ffi clock targetConfig) (source.map (compileDec cfg2))).1.ffi := by
    intro clock
    cases run : FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source with
    | mk sourceState sourceResult =>
      have sourceSafe : sourceResult ≠ some (.abort .typeError) := by simpa [run] using safe clock
      obtain ⟨targetState, targetResult, targetRun, results, finalStates⟩ :=
        (compileExps_evaluate cfg).2 _ source _ sourceState cfg2 _ sourceResult
          ⟨run, rfl, stateRel_initial cfg ffi clock sourceConfig targetConfig configs, sourceSafe⟩
      simpa [run, targetRun] using And.intro results finalStates.2.2.1.symm
  have targetSafe : ∀ clock,
      (FlatSem.evaluateDecs (FlatSem.initialState ffi clock targetConfig) (source.map (compileDec cfg2))).2 ≠
        some (.abort .typeError) := by
    intro clock
    exact outcomeRel_noTypeError _ _ (observations clock).1 (safe clock)
  have terminatingEq : FlatSem.terminatingObservation sourceConfig ffi source =
      FlatSem.terminatingObservation targetConfig ffi (source.map (compileDec cfg2)) := by
    funext behavior
    apply propext
    constructor
    · rintro ⟨clock, state, result, outcome, run, outcomeEq, behaviorEq⟩
      have observed := observations clock
      rw [run] at observed
      refine ⟨clock, (FlatSem.evaluateDecs (FlatSem.initialState ffi clock targetConfig) (source.map (compileDec cfg2))).1,
        (FlatSem.evaluateDecs (FlatSem.initialState ffi clock targetConfig) (source.map (compileDec cfg2))).2, outcome,
        Prod.eta _, ?_, ?_⟩
      · change outcomeObservation _ outcome
        apply (outcomeRel_observation _ _ observed.1 outcome).1
        exact outcomeEq
      · simpa [← observed.2] using behaviorEq
    · rintro ⟨clock, state, result, outcome, run, outcomeEq, behaviorEq⟩
      have observed := observations clock
      rw [run] at observed
      refine ⟨clock, (FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source).1,
        (FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source).2, outcome,
        Prod.eta _, ?_, ?_⟩
      · change outcomeObservation _ outcome
        apply (outcomeRel_observation _ _ observed.1 outcome).2
        exact outcomeEq
      · simpa [observed.2] using behaviorEq
  have tracesEq :
      (fun trace => ∃ clock, trace = HolLList.fromList (FlatSem.evaluateDecs
        (FlatSem.initialState ffi clock sourceConfig) source).1.ffi.ioEvents) =
      (fun trace => ∃ clock, trace = HolLList.fromList (FlatSem.evaluateDecs
        (FlatSem.initialState ffi clock targetConfig) (source.map (compileDec cfg2))).1.ffi.ioEvents) := by
    funext trace
    apply propext
    constructor <;> rintro ⟨clock, h⟩ <;> refine ⟨clock, ?_⟩
    · simpa [(observations clock).2] using h
    · simpa [← (observations clock).2] using h
  unfold FlatSem.semantics
  have sourceNoError : ¬ ∃ clock, (FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source).2 =
      some (.abort .typeError) := fun ⟨clock, error⟩ => safe clock error
  have targetNoError : ¬ ∃ clock, (FlatSem.evaluateDecs (FlatSem.initialState ffi clock targetConfig)
      (source.map (compileDec cfg2))).2 = some (.abort .typeError) := fun ⟨clock, error⟩ => targetSafe clock error
  simp only [sourceNoError, targetNoError, if_false]
  rw [terminatingEq, tracesEq]

end Flapjack.Compiler.Backend.FlatPattern
