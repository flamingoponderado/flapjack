import Flapjack.Compiler.Backend.FlatToClos.Proofs.Executable
import Flapjack.Compiler.Backend.ClosInterp.Proofs.AttachSemantics

/-!
Observational composition of the proof-side flat-to-closure evaluator and
interpreter attachment. The evaluator and its relations still require HOL
correspondence review.
-/
namespace Flapjack.Compiler.Backend.FlatToClos

open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps

private def flatOutcome (flat : Option (ErrorResult FlatSem.Value)) (outcome : HolOutcome) : Prop :=
  match flat with
  | some (.abort (.ffiError event)) => outcome = .ffiOutcome event
  | some (.abort _) => False
  | _ => outcome = .success

private def closOutcome (clos : Result (List ClosSem.Value) ClosSem.Value) (outcome : HolOutcome) : Prop :=
  match clos with
  | .err (.abort .timeoutError) => False
  | .err (.abort (.ffiError event)) => outcome = .ffiOutcome event
  | _ => outcome = .success

/-- Related declaration results make the same terminating-outcome decision
when the flat evaluator does not report a type error. -/
theorem decResultRel_outcome
    (flat : Option (ErrorResult FlatSem.Value)) (clos : Result (List ClosSem.Value) ClosSem.Value)
    (related : DecResultRel flat clos) (safe : flat ≠ some (.abort .typeError)) (outcome : HolOutcome) :
    flatOutcome flat outcome ↔ closOutcome clos outcome := by
  cases related with
  | success values => rfl
  | raise rel => rfl
  | abort error =>
    cases error with
    | typeError => exact False.elim (safe rfl)
    | timeoutError => rfl
    | ffiError event => rfl

/-- Adding the initializer's unit value does not affect declaration result
correspondence. -/
theorem decResultRel_init (flat : Option (ErrorResult FlatSem.Value))
    (clos : Result (List ClosSem.Value) ClosSem.Value) (related : DecResultRel flat clos) :
    DecResultRel flat (match clos with
      | .val values => .val (ClosSem.unitValue :: values)
      | .err error => .err error) := by
  cases related with
  | success values => exact .success _
  | raise rel => exact .raise rel
  | abort error => exact .abort error

/-- For every clock, the flat and compiled closure programs have related
results and identical FFI state. -/
theorem compileProg_clock_observation {C F : Type} (ffi : HolFfiState F)
    (maxApp : Nat) (config : FlatSem.InstallConfig C) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C) (decs : List FlatLang.Exp)
    (positive : 0 < maxApp) (install : installConfigRel config oracle compiler)
    (matchFree : FlatProps.noMatDecs decs = true)
    (safe : FlatSem.semantics config ffi decs ≠ .fail) (clock : Nat) :
    let flat := FlatSem.evaluateDecs (FlatSem.initialState ffi clock config) decs
    let clos := ClosSem.evaluate (compileProg decs) []
      (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle compiler clock)
    DecResultRel flat.2 clos.1 ∧ flat.1.ffi = clos.2.ffi := by
  have noTypeError : (FlatSem.evaluateDecs (FlatSem.initialState ffi clock config) decs).2 ≠
      some (.abort .typeError) := by
    intro failure
    apply safe
    simp [FlatSem.semantics, show ∃ k,
      (FlatSem.evaluateDecs (FlatSem.initialState ffi k config) decs).2 = some (.abort .typeError) from ⟨clock, failure⟩]
  obtain ⟨result, target, relation, states, run⟩ :=
    compileProg_evaluate_related ffi maxApp clock config oracle compiler decs positive install matchFree noTypeError
  have rel := decResultRel_init _ _ relation
  have ffiEq := states.2.1
  rw [run]
  cases result <;> exact ⟨by simpa using rel, ffiEq⟩

/-- Non-failing match-free flat programs and their closure compilation have
the same proof-side observable behavior. This is not tagged as the HOL theorem
until the underlying evaluators and relations have been reviewed. -/
theorem compileProg_semantics_proofSide {C F : Type} (ffi : HolFfiState F)
    (maxApp : Nat) (config : FlatSem.InstallConfig C) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C) (decs : List FlatLang.Exp)
    (positive : 0 < maxApp) (install : installConfigRel config oracle compiler)
    (matchFree : FlatProps.noMatDecs decs = true)
    (safe : FlatSem.semantics config ffi decs ≠ .fail) :
    ClosSem.semantics ffi maxApp HolFiniteMapExact.empty oracle compiler (compileProg decs) =
      FlatSem.semantics config ffi decs := by
  classical
  let flat := fun clock => FlatSem.evaluateDecs (FlatSem.initialState ffi clock config) decs
  let clos := fun clock => ClosSem.evaluate (compileProg decs) []
    (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle compiler clock)
  have observations : ∀ clock, DecResultRel (flat clock).2 (clos clock).1 ∧
      (flat clock).1.ffi = (clos clock).2.ffi := by
    intro clock
    exact compileProg_clock_observation ffi maxApp config oracle compiler decs positive install matchFree safe clock
  have flatSafe : ∀ clock, (flat clock).2 ≠ some (.abort .typeError) := by
    intro clock failure
    apply safe
    simp [FlatSem.semantics, show ∃ k, (flat k).2 = some (.abort .typeError) from ⟨clock, failure⟩, flat]
  have closSafe : ∀ clock, (clos clock).1 ≠ .err (.abort .typeError) := by
    intro clock failure
    have rel := (observations clock).1
    generalize fEq : (flat clock).2 = f at rel
    generalize cEq : (clos clock).1 = c at rel
    rw [cEq] at failure
    have fsafe : f ≠ some (.abort .typeError) := by simpa [← fEq] using flatSafe clock
    cases rel with
    | success values => simp at failure
    | raise related => simp at failure
    | abort error =>
      have : error = .typeError := by simpa using failure
      subst error
      exact fsafe rfl
  have termEq : FlatSem.terminatingObservation config ffi decs =
      ClosSem.terminatingObservation ffi maxApp HolFiniteMapExact.empty oracle compiler (compileProg decs) := by
    funext behavior
    apply propext
    constructor
    · rintro ⟨clock, state, result, outcome, run, shape, behaviorEq⟩
      have obs := observations clock
      change FlatSem.evaluateDecs (FlatSem.initialState ffi clock config) decs = _ at run
      change DecResultRel (flat clock).2 (clos clock).1 ∧ (flat clock).1.ffi = (clos clock).2.ffi at obs
      have flatEq : flat clock = (state, result) := run
      rw [flatEq] at obs
      refine ⟨clock, (clos clock).1, (clos clock).2, outcome, ?_, ?_, ?_⟩
      · exact Prod.eta (clos clock)
      · have shape' : flatOutcome result outcome := by
          cases result with
          | none => exact shape
          | some error => cases error with
            | raise value => exact shape
            | abort error => cases error <;> exact shape
        have target := (decResultRel_outcome result (clos clock).1 obs.1 (by simpa [flatEq] using flatSafe clock) outcome).mp shape'
        cases h : (clos clock).1 with
        | val values => simpa [closOutcome, h] using target
        | err error => cases error with
          | raise value => simpa [closOutcome, h] using target
          | abort error => cases error <;> simp [closOutcome, h] at target ⊢ <;> exact target
      · rw [← obs.2]
        exact behaviorEq
    · rintro ⟨clock, result, state, outcome, run, shape, behaviorEq⟩
      have obs := observations clock
      have closEq : clos clock = (result, state) := run
      rw [closEq] at obs
      refine ⟨clock, (flat clock).1, (flat clock).2, outcome, ?_, ?_, ?_⟩
      · exact Prod.eta (flat clock)
      · have shape' : closOutcome result outcome := by
          cases result with
          | val values => exact shape
          | err error => cases error with
            | raise value => exact shape
            | abort error => cases error <;> exact shape
        have target := (decResultRel_outcome (flat clock).2 result obs.1 (flatSafe clock) outcome).mpr shape'
        cases h : (flat clock).2 with
        | none => simpa [flatOutcome, h] using target
        | some error => cases error with
          | raise value => simpa [flatOutcome, h] using target
          | abort error =>
            cases error <;> simp [flatOutcome, h] at target ⊢
            all_goals exact target
      · rw [obs.2]
        exact behaviorEq
  have tracesEq :
      (fun trace => ∃ clock, trace = HolLList.fromList (flat clock).1.ffi.ioEvents) =
      (fun trace => ∃ clock, trace = HolLList.fromList (clos clock).2.ffi.ioEvents) := by
    funext trace
    apply propext
    constructor <;> rintro ⟨clock, h⟩ <;> refine ⟨clock, ?_⟩
    · simpa [(observations clock).2] using h
    · simpa [← (observations clock).2] using h
  unfold FlatSem.semantics ClosSem.semantics
  have fNo : ¬ ∃ clock, (flat clock).2 = some (.abort .typeError) := fun ⟨k, h⟩ => flatSafe k h
  have cNo : ¬ ∃ clock, (clos clock).1 = .err (.abort .typeError) := fun ⟨k, h⟩ => closSafe k h
  change (if ∃ clock, (clos clock).1 = .err (.abort .typeError) then _ else _) =
    (if ∃ clock, (flat clock).2 = some (.abort .typeError) then _ else _)
  simp only [fNo, cNo, if_false]
  dsimp only [flat, clos] at tracesEq
  rw [termEq, tracesEq]
  rfl

/-- Under the factored source precondition and actual incremental compiler
callback, the production closure semantics is an observable source behavior.
The component relations and semantics remain subject to HOL correspondence
review, and the rest of the backend is not covered here. -/
theorem sourceCompileProg_semantics_proofSide {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (SourceToFlat.Config × C)))
    (transform : List AstHOL.Dec → List AstHOL.Dec)
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig C) (compiler : ClosSem.Compiler C)
    (declarations : List AstHOL.Dec) (maxApp : Nat)
    (precondition : SourceToFlat.FactoredPrecondition interp transform source sourceEnv sourceConfig flatConfig declarations)
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < maxApp)
    (production : flatConfig.compile = pureCc incCompileDecs compiler) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
      (ClosSem.semantics source.ffi maxApp HolFiniteMapExact.empty
        (pureCo incCompileDecs ∘ flatConfig.compileOracle) compiler
        (compileProg (SourceToFlat.compileTotal sourceConfig declarations).2)) := by
  let code := (SourceToFlat.compileTotal sourceConfig declarations).2
  let oracle := pureCo incCompileDecsProofSide ∘ flatConfig.compileOracle
  let intermediateCompiler := pureCc ClosInterp.insertProgram compiler
  have sourceSem := SourceToFlat.factoredCompile_semantics interp transform source sourceEnv sourceConfig
    flatConfig declarations precondition safe
  have flatSafe : FlatSem.semantics flatConfig source.ffi code ≠ .fail := by
    intro failure
    apply safe
    simpa [code, failure] using sourceSem
  have install : installConfigRel flatConfig oracle intermediateCompiler :=
    production_installConfigRel flatConfig compiler
      (sourcePrecondition_oracle_noMat interp transform source sourceEnv sourceConfig flatConfig declarations precondition)
      production
  have flatClos := compileProg_semantics_proofSide source.ffi maxApp flatConfig oracle
    intermediateCompiler code positive install (SourceToFlat.noMat_compileTotal sourceConfig declarations) flatSafe
  have intermediateSafe : ClosSem.semantics source.ffi maxApp HolFiniteMapExact.empty oracle
      intermediateCompiler (compileProg code) ≠ .fail := by
    rw [flatClos]
    exact flatSafe
  have oracleSafe : ∀ index, (oracle index).2.2 = [] := by
    intro index
    cases h : flatConfig.compileOracle index
    simp [oracle, pureCo, h, incCompileDecsProofSide]
  have attachment := ClosInterp.attachInterpreter_semantics (compileDecs code) source.ffi maxApp oracle compiler
    (by simpa [compileProg, intermediateCompiler] using intermediateSafe) ⟨oracleSafe, positive⟩
  have complete : ClosSem.semantics source.ffi maxApp HolFiniteMapExact.empty
      (pureCo incCompileDecs ∘ flatConfig.compileOracle) compiler (compileProg code) =
      FlatSem.semantics flatConfig source.ffi code := by
    calc
      _ = ClosSem.semantics source.ffi maxApp HolFiniteMapExact.empty oracle intermediateCompiler (compileProg code) := by
        simpa [oracle, intermediateCompiler, compileProg, incrementalOracle_factor] using attachment
      _ = _ := flatClos
  rw [← complete] at sourceSem
  exact sourceSem

end Flapjack.Compiler.Backend.FlatToClos
