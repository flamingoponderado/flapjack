import Flapjack.Compiler.Backend.FlatToClos.Proofs.Install
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Declarations

/-! Dynamic Eval/Install composition for the proof-side simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL

/-- The closure evaluator's continuation after installation. -/
noncomputable def runInstalled {C F : Type} (values : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.EvalResult C F :=
  match ClosSem.doInstall values state with
  | (.err error, next) => (.err error, next)
  | (.val program, next) =>
    let (result, last) := ClosSem.evaluate program [] next
    match result with
    | .err error => (.err error, last)
    | .val values => (.val [@Flapjack.holLast ClosSem.Value ⟨ClosSem.unitValue⟩ values], last)

/-- The Install expression evaluates its arguments before running the
installation continuation. -/
theorem evaluate_install {C F : Type} (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (env : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluate [.op trace .install args] env state =
      match ClosSem.evaluate args env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => runInstalled values.reverse next := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  cases evaluated : ClosSem.evaluate args env state with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values =>
      dsimp only
      unfold runInstalled
      split <;> simp_all
      split <;> simp_all
      rfl

/-- The flat evaluator's continuation after a successful Eval request. -/
noncomputable def runFlatEval {C F : Type} (state : FlatSem.State C F)
    (config : FlatSem.InstallConfig C) (declarations : List FlatLang.Exp) : FlatSem.EvalResult C F :=
  let updated := { state with evalConfig := config }
  if updated.clock = 0 then (updated, .err (.abort .timeoutError)) else
    let (last, result) := FlatSem.evaluateDecs (FlatSem.decClock updated) declarations
    match result with
    | none => (last, .val [FlatSem.unitValue])
    | some error => (last, .err error)

/-- The flat Eval expression evaluates arguments first and then runs the
successful dynamic-evaluation continuation. -/
theorem evaluate_eval {C F : Type} (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) :
    FlatSem.evaluate env state [.app trace (.src .eval) args] =
      match FlatSem.evaluate env state args.reverse with
      | (next, .err error) => (next, .err error)
      | (next, .val values) =>
        match FlatSem.doEval values.reverse next.evalConfig with
        | none => (next, .err (.abort .typeError))
        | some (decs, config, _) => runFlatEval next config decs := by
  rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations env state args.reverse (.lit .none (.intLit 0)) []).1]
  cases evaluated : FlatSem.evaluate env state args.reverse with
  | mk next result =>
    cases result with
    | err error => rfl
    | val values =>
      dsimp only
      cases run : FlatSem.doEval values.reverse next.evalConfig with
      | none => simp
      | some result =>
        obtain ⟨decs, config, value⟩ := result
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, valueEq⟩ :=
          doEval_success_parts values.reverse next.evalConfig config decs value run
        subst value
        simp [runFlatEval]
        split <;> rfl

/-- The original `LAST` observation of a unit-terminated list is unit. -/
theorem holLast_append_unit (values : List ClosSem.Value) :
    @Flapjack.holLast ClosSem.Value ⟨ClosSem.unitValue⟩ (values ++ [ClosSem.unitValue]) = ClosSem.unitValue := by
  let _ : Nonempty ClosSem.Value := ⟨ClosSem.unitValue⟩
  induction values with
  | nil => simp [Flapjack.holLast]
  | cons first rest ih =>
    rw [List.cons_append, Flapjack.holLast_cons]
    simp [ih]

/-- Successful flat Eval and closure Install requests execute related
unit-terminated declarations and produce related results. The declaration
simulation is the induction hypothesis; semantic correspondence remains open. -/
theorem eval_install_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (sourceValues : List FlatSem.Value) (targetValues : List ClosSem.Value)
    (decs : List FlatLang.Exp) (config : FlatSem.InstallConfig C) (value : FlatSem.Value)
    (run : FlatSem.doEval sourceValues source.evalConfig = some (decs, config, value))
    (states : StateRel source target) (values : List.Forall₂ ValueRel sourceValues targetValues)
    (decsSim : ∀ (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      StateRel next nextTarget → FlatProps.noMatDecs decs = true →
      (FlatSem.evaluateDecs next decs).2 ≠ some (.abort .typeError) → DecUnitSim next nextTarget decs)
    (notTypeError : (runFlatEval source config decs).2 ≠ .err (.abort .typeError)) :
    StateRel (runFlatEval source config decs).1 (runInstalled targetValues target).2 ∧
      EvalResultRel (runFlatEval source config decs).2 (runInstalled targetValues target).1 := by
  obtain ⟨advanced, advancedRel, valueEq, safe, install⟩ :=
    doEval_install source target sourceValues targetValues decs config value run states values
  have clocks := states.2.2.1
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by omega
    have unchanged : FlatSem.decClock { source with evalConfig := config } = { source with evalConfig := config } := by
      cases source
      simp_all [FlatSem.decClock]
    have rel := stateRel_decClock advancedRel
    rw [unchanged] at rel
    simp [runFlatEval, runInstalled, install, zero, targetZero, EvalResultRel.abort]
    simpa [zero] using rel
  · have targetNonzero : target.clock ≠ 0 := by omega
    have rel := stateRel_decClock advancedRel
    simp only [runFlatEval, zero, ↓reduceIte] at notTypeError ⊢
    simp only [runInstalled, install, targetNonzero, ↓reduceIte] at ⊢
    have decsNot : (FlatSem.evaluateDecs (FlatSem.decClock { source with evalConfig := config }) decs).2 ≠
        some (.abort .typeError) := by
      intro bad
      simp [bad] at notTypeError
    have simulated := decsSim _ _ rel safe decsNot
    simp only [DecUnitSim] at simulated
    cases flatRun : FlatSem.evaluateDecs (FlatSem.decClock { source with evalConfig := config }) decs with
    | mk last flatResult =>
      cases closRun : ClosSem.evaluate (compileDecs decs ++ compileDecs [.con .none none []]) []
          (ClosSem.decClock 1 advanced) with
      | mk closResult lastTarget =>
        simp only [flatRun, closRun] at simulated ⊢
        rcases simulated with ⟨lastRel, results⟩
        cases results with
        | success prior =>
          change StateRel last lastTarget ∧ EvalResultRel (.val [FlatSem.unitValue])
            (.val [@Flapjack.holLast ClosSem.Value ⟨ClosSem.unitValue⟩ (prior ++ [ClosSem.unitValue])])
          rw [holLast_append_unit]
          exact ⟨lastRel, .value (.cons (.tuple .nil) .nil)⟩
        | raise related => exact ⟨lastRel, .raise related⟩
        | abort error => exact ⟨lastRel, .abort error⟩

/-- Simulate an Eval expression after simulating its reversed argument list
and the declarations selected by its compiler oracle. -/
theorem evaluate_eval_related {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : EvalSim env names values source target args.reverse)
    (decsSim : ∀ (decs : List FlatLang.Exp) (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      StateRel next nextTarget → FlatProps.noMatDecs decs = true →
      (FlatSem.evaluateDecs next decs).2 ≠ some (.abort .typeError) → DecUnitSim next nextTarget decs)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .eval) args]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .eval) args] := by
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps_reverse] at argsSim
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  rw [evaluate_eval] at notTypeError ⊢
  rw [evaluate_install]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argsSim notTypeError ⊢
      rcases argsSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        cases run : FlatSem.doEval sourceArgs.reverse next.evalConfig with
        | none => simp [run] at notTypeError
        | some result =>
          obtain ⟨decs, config, value⟩ := result
          simp only [run] at notTypeError ⊢
          exact eval_install_related next nextTarget _ _ decs config value run states
            (List.rel_reverse related) (decsSim decs) notTypeError

end Flapjack.Compiler.Backend.FlatToClos
