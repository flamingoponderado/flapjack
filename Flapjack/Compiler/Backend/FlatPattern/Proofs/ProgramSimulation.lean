import Flapjack.Compiler.Backend.FlatPattern.Proofs.ClockedInduction
import Flapjack.Compiler.Backend.FlatProps.EvalSim

/-! Program-level simulation for the proof-side flat pattern compiler. The
evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend

/-- Related installation configurations and compiled declarations give a
program evaluation simulation with no additional target clock. This is
Flapjack proof-side infrastructure until the evaluator and value relation are
reviewed against HOL. -/
theorem compileDecs_evalSim_proofSide {C F : Type} (cfg cfg2 : Config) (ffi : HolFfiState F)
    (source target : List FlatLang.Exp) (sourceConfig targetConfig : FlatSem.InstallConfig C)
    (configs : installConfRel cfg sourceConfig targetConfig) :
    FlatProps.evalSim ffi source target sourceConfig targetConfig
      (fun decs decs' => decs.map (compileDec cfg2) = decs') false := by
  intro clock sourceResult sourceState run safe programs
  have sourceSafe : sourceResult ≠ some (.abort .typeError) := by simpa using safe
  subst target
  have states := stateRel_initial cfg ffi clock sourceConfig targetConfig configs
  obtain ⟨targetState, targetResult, targetRun, finalStates, results⟩ :=
    evaluateDecs_simulation_all cfg2 cfg _ _ sourceState source sourceResult states run sourceSafe
  refine ⟨0, targetResult, targetState, by simpa using targetRun, finalStates.2.2.1.symm, ?_, ?_, ?_⟩
  · intro isNone
    subst sourceResult
    cases targetResult <;> simp_all [optionRel]
  · intro value isRaise
    subst sourceResult
    cases targetResult with
    | none => simp [optionRel] at results
    | some error =>
      cases results with
      | raise values => exact ⟨_, rfl⟩
  · intro abort isAbort
    subst sourceResult
    cases targetResult with
    | none => simp [optionRel] at results
    | some error =>
      cases results with
      | abort reason => rfl

/-- The observable termination class of a declaration result. -/
def outcomeObservation (result : Option (SemanticPrimitivesHOL.ErrorResult FlatSem.Value)) (outcome : HolOutcome) : Prop :=
  match result with
  | some (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
  | some (.abort _) => False
  | _ => outcome = HolOutcome.success

/-- The factored outcome predicate has the same cases as the observation. -/
theorem outcomeObservation_cases (result : Option (SemanticPrimitivesHOL.ErrorResult FlatSem.Value)) (outcome : HolOutcome) :
    (match result, outcome with
     | some (.abort (.ffiError event)), outcome => outcome = HolOutcome.ffiOutcome event
     | some (.abort _), _ => False
     | _, outcome => outcome = HolOutcome.success) ↔ outcomeObservation result outcome := by
  cases result with
  | none => rfl
  | some error => cases error with
    | raise value => rfl
    | abort reason => cases reason <;> rfl

/-- Related declaration outcomes have the same observable termination class. -/
theorem outcomeRel_observation (source target : Option (SemanticPrimitivesHOL.ErrorResult FlatSem.Value))
    (related : optionRel FlatErrorRel source target) (outcome : HolOutcome) :
    outcomeObservation source outcome ↔ outcomeObservation target outcome := by
  cases source with
  | none => cases target <;> simp_all [optionRel, outcomeObservation]
  | some sourceError =>
    cases target with
    | none => simp [optionRel] at related
    | some targetError =>
      cases related with
      | raise values => rfl
      | abort reason => cases reason <;> rfl

/-- A related optional outcome cannot introduce a type error. -/
theorem outcomeRel_noTypeError (source target : Option (SemanticPrimitivesHOL.ErrorResult FlatSem.Value))
    (related : optionRel FlatErrorRel source target) (safe : source ≠ some (.abort .typeError)) :
    target ≠ some (.abort .typeError) := by
  intro bad
  subst target
  cases source with
  | none => simp [optionRel] at related
  | some error =>
    cases related with
    | abort reason => exact safe rfl

/-- If every source clock avoids type errors, compiled declarations have the
same proof-side observational behavior. The equality does not claim HOL
correspondence for the evaluator or relations used here. -/
theorem compileDecs_semantics_of_safe {C F : Type} (cfg cfg2 : Config) (ffi : HolFfiState F)
    (source : List FlatLang.Exp) (sourceConfig targetConfig : FlatSem.InstallConfig C)
    (configs : installConfRel cfg sourceConfig targetConfig)
    (safe : ∀ clock, (FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source).2 ≠
      some (.abort .typeError)) :
    FlatSem.semantics sourceConfig ffi source = FlatSem.semantics targetConfig ffi (source.map (compileDec cfg2)) := by
  classical
  have observations : ∀ clock,
      optionRel FlatErrorRel
        (FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source).2
        (FlatSem.evaluateDecs (FlatSem.initialState ffi clock targetConfig) (source.map (compileDec cfg2))).2 ∧
      (FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source).1.ffi =
        (FlatSem.evaluateDecs (FlatSem.initialState ffi clock targetConfig) (source.map (compileDec cfg2))).1.ffi := by
    intro clock
    cases run : FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source with
    | mk sourceState sourceResult =>
      have sourceSafe : sourceResult ≠ some (.abort .typeError) := by simpa [run] using safe clock
      obtain ⟨targetState, targetResult, targetRun, finalStates, results⟩ :=
        evaluateDecs_simulation_all cfg2 cfg _ _ sourceState source sourceResult
          (stateRel_initial cfg ffi clock sourceConfig targetConfig configs) run sourceSafe
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
      · apply (outcomeObservation_cases _ outcome).2
        apply (outcomeRel_observation _ _ observed.1 outcome).1
        exact (outcomeObservation_cases result outcome).1 outcomeEq
      · simpa [← observed.2] using behaviorEq
    · rintro ⟨clock, state, result, outcome, run, outcomeEq, behaviorEq⟩
      have observed := observations clock
      rw [run] at observed
      refine ⟨clock, (FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source).1,
        (FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source).2, outcome,
        Prod.eta _, ?_, ?_⟩
      · apply (outcomeObservation_cases _ outcome).2
        apply (outcomeRel_observation _ _ observed.1 outcome).2
        exact (outcomeObservation_cases result outcome).1 outcomeEq
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

/-- A non-failing source program and related installation configurations
have the same proof-side observational behavior after pattern compilation.
This is not tagged as the HOL semantics theorem because the evaluator and
relations have not completed cross-language review. -/
theorem compileDecs_semantics_proofSide {C F : Type} (cfg cfg2 : Config) (ffi : HolFfiState F)
    (source : List FlatLang.Exp) (sourceConfig targetConfig : FlatSem.InstallConfig C)
    (configs : installConfRel cfg sourceConfig targetConfig)
    (notFail : FlatSem.semantics sourceConfig ffi source ≠ .fail) :
    FlatSem.semantics sourceConfig ffi source = FlatSem.semantics targetConfig ffi (source.map (compileDec cfg2)) := by
  apply compileDecs_semantics_of_safe cfg cfg2 ffi source sourceConfig targetConfig configs
  intro clock error
  have failure : FlatSem.semantics sourceConfig ffi source = .fail := by
    unfold FlatSem.semantics
    simp [show ∃ clock, (FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source).2 =
      some (.abort .typeError) from ⟨clock, error⟩]
  exact notFail failure

end Flapjack.Compiler.Backend.FlatPattern
