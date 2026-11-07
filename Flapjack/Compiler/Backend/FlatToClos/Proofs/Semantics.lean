import Flapjack.Compiler.Backend.FlatToClos.Proofs.Executable
import Flapjack.Compiler.Backend.FlatToClos.Proofs.CompileCorrectShape
import Flapjack.Compiler.Backend.ClosInterp.Proofs.AttachSemanticsSource
import Flapjack.FiniteMap.EmptyExact

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
  simp only [fNo, cNo, ite_false]
  dsimp only [flat, clos] at tracesEq
  rw [termEq, tracesEq]
  rfl

/-- The original primed observational theorem, with its three premises
grouped as in the source. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "compile_semantics'"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem compileSemantics_prime_source {C F : Type} (ffi : HolFfiState F)
    (maxApp : Nat) (config : FlatSem.InstallConfig C) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C) (decs : List FlatLang.Exp) :
    0 < maxApp ∧ FlatProps.noMatDecs decs = true ∧ installConfigRel config oracle compiler →
    FlatSem.semantics config ffi decs ≠ .fail →
    ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty oracle compiler (compileProg decs) =
      FlatSem.semantics config ffi decs := by
  rintro ⟨positive, matchFree, install⟩ safe
  exact compileProg_semantics_proofSide ffi maxApp config oracle compiler decs positive install matchFree safe

/-- The production incremental compiler's installation relation. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "install_config_rel_def"]
def installConfigRelProduction {C OraclePayload CompilerPayload : Type} (source : FlatSem.InstallConfig C)
    (oracle : Nat → C × (List ClosLang.Exp × List OraclePayload))
    (compiler : C → (List ClosLang.Exp × List CompilerPayload) →
      Option (List (BitVec 8) × List (BitVec 64) × C)) : Prop :=
  (∀ index, FlatProps.noMatDecs (source.compileOracle index).2 = true) ∧
  oracle = pureCo incCompileDecs ∘ source.compileOracle ∧
  source.compile = pureCc incCompileDecs compiler

/-- Production flat-to-closure observational semantics under the original
installation relation. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "compile_semantics"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem compileSemantics_source {C F : Type} (ffi : HolFfiState F)
    (maxApp : Nat) (config : FlatSem.InstallConfig C) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C) (decs : List FlatLang.Exp) :
    0 < maxApp ∧ FlatProps.noMatDecs decs = true ∧ installConfigRelProduction config oracle compiler →
    FlatSem.semantics config ffi decs ≠ .fail →
    ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty oracle compiler (compileProg decs) =
      FlatSem.semantics config ffi decs := by
  rintro ⟨positive, matchFree, oracleSafe, oracleEq, compilerEq⟩ safe
  let initialOracle : ClosSem.CompileOracle C := pureCo incCompileDecsProofSide ∘ config.compileOracle
  let initialCompiler := pureCc ClosInterp.insertProgram compiler
  have install : installConfigRel config initialOracle initialCompiler :=
    production_installConfigRel config compiler oracleSafe compilerEq
  have flatClos := compileProg_semantics_proofSide ffi maxApp config initialOracle initialCompiler decs
    positive install matchFree safe
  have initialSafe : ClosSem.semantics ffi maxApp HolFiniteMapExact.empty initialOracle
      initialCompiler (compileProg decs) ≠ .fail := by
    rw [flatClos]
    exact safe
  have emptyAux : ∀ index, (initialOracle index).2.2 = [] := by
    intro index
    cases h : config.compileOracle index
    simp [initialOracle, pureCo, h, incCompileDecsProofSide]
  have attachment := ClosInterp.attachInterpreter_semantics_source (compileDecs decs) ffi maxApp initialOracle compiler
    (by simpa [compileProg, initialCompiler, HolFiniteMapExact.holEmpty] using initialSafe) ⟨emptyAux, positive⟩
  have complete : ClosSem.semantics ffi maxApp HolFiniteMapExact.empty
      (pureCo incCompileDecs ∘ config.compileOracle) compiler (compileProg decs) =
      FlatSem.semantics config ffi decs := by
    calc
      _ = ClosSem.semantics ffi maxApp HolFiniteMapExact.empty initialOracle initialCompiler (compileProg decs) := by
        simpa [initialOracle, initialCompiler, compileProg, incrementalOracle_factor, HolFiniteMapExact.holEmpty] using attachment
      _ = _ := flatClos
  simpa [oracleEq, HolFiniteMapExact.holEmpty] using complete

end Flapjack.Compiler.Backend.FlatToClos
