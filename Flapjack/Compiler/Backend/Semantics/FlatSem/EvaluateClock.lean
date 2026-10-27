import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyClock
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact
import Lean.Elab.Tactic.Omega

/-! Clock-preservation prerequisites for flat evaluation. The full mutual
evaluator clock theorem remains open. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL

/-- Lifting a primitive result cannot change the evaluator clock. -/
theorem applyResult_clock {C F : Type} (state : State C F) (op : FlatLang.Op)
    (values : List Value) : (applyResult state op values).1.clock = state.clock := by
  unfold applyResult
  cases run : doApp state op values with
  | none => simp
  | some pair =>
    obtain ⟨next, result⟩ := pair
    have clock := doApp_clock state next op values result run
    cases result <;> simpa using clock

/-- Evaluating a constructor preserves the bound when its argument list does. -/
theorem evaluate_con_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (constructor : Option (FlatLang.CtorId × FlatLang.TypeId))
    (args : List FlatLang.Exp) (argumentClock : (evaluate env state args.reverse).1.clock ≤ state.clock) :
    (evaluate env state [.con trace constructor args]).1.clock ≤ state.clock := by
  rw [evaluate]
  generalize h : evaluate env state args.reverse = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  cases result <;> exact argumentClock

/-- Evaluating a raise preserves the bound when its operand does. -/
theorem evaluate_raise_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (body : FlatLang.Exp)
    (operandClock : (evaluate env state [body]).1.clock ≤ state.clock) :
    (evaluate env state [.raise trace body]).1.clock ≤ state.clock := by
  rw [evaluate]
  generalize h : evaluate env state [body] = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  cases result <;> exact operandClock

/-- Evaluating a list of at least two expressions preserves the bound when
its tail does after the first result's clock clamp. -/
theorem evaluate_list_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (first second : FlatLang.Exp) (rest : List FlatLang.Exp)
    (tailClock : ∀ next : State C F, next.clock ≤ state.clock →
      (evaluate env next (second :: rest)).1.clock ≤ next.clock) :
    (evaluate env state (first :: second :: rest)).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state [first])
  rw [evaluate]
  generalize h : fixClock state (evaluate env state [first]) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    have tailBound := Nat.le_trans (tailClock next bound) bound
    generalize tailRun : evaluate env next (second :: rest) = tailResult at *
    obtain ⟨last, result⟩ := tailResult
    cases result <;> exact tailBound

/-- A declaration list preserves the bound when the remaining declarations
do after the first result's clock clamp. -/
theorem evaluate_decs_clock_step {C F : Type} (state : State C F)
    (declaration : FlatLang.Exp) (rest : List FlatLang.Exp)
    (tailClock : ∀ next : State C F, next.clock ≤ state.clock →
      (evaluateDecs next rest).1.clock ≤ next.clock) :
    (evaluateDecs state (declaration :: rest)).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate ⟨[]⟩ state [declaration])
  rw [evaluateDecs]
  generalize h : fixClock state (evaluate ⟨[]⟩ state [declaration]) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    have tailBound := Nat.le_trans (tailClock next bound) bound
    split <;> assumption

/-- Flat-specific applications cannot increase the clock, regardless of the
outcome of evaluating their arguments. -/
theorem evaluate_flatApp_clock {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (op : FlatLang.Op) (args : List FlatLang.Exp)
    (flatOp : ∀ source, op ≠ .src source) :
    (evaluate env state [.app trace op args]).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state args.reverse)
  rw [evaluate]
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    cases op with
    | src source => exact (flatOp source rfl).elim
    | globalVarAlloc n => simpa [applyResult_clock] using bound
    | globalVarInit n => simpa [applyResult_clock] using bound
    | globalVarLookup n => simpa [applyResult_clock] using bound
    | tagLenEq tag length => simpa [applyResult_clock] using bound
    | lenEq length => simpa [applyResult_clock] using bound
    | el n => simpa [applyResult_clock] using bound
    | id => simpa [applyResult_clock] using bound

/-- Source primitive applications other than calls, dynamic evaluation, and
thunk forcing cannot increase the clock. -/
theorem evaluate_simpleSourceApp_clock {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (op : Flapjack.AstHOL.Op) (args : List FlatLang.Exp)
    (notCall : op ≠ .opapp) (notEval : op ≠ .eval) (notForce : op ≠ .thunkOp .forceThunk) :
    (evaluate env state [.app trace (.src op) args]).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state args.reverse)
  rw [evaluate]
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  cases result with
  | err error => exact bound
  | val values =>
    cases op <;> simp_all [applyResult_clock]

/-- A function application preserves the incoming clock bound when recursive
evaluations at smaller clocks do. This is an induction step for the full
clock theorem, not the full theorem itself. -/
theorem evaluate_call_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (smallerClock : ∀ (newEnv : Environment Value) (newState : State C F) (body : FlatLang.Exp),
      newState.clock < state.clock → (evaluate newEnv newState [body]).1.clock ≤ newState.clock) :
    (evaluate env state [.app trace (.src .opapp) args]).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state args.reverse)
  rw [evaluate]
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    cases call : doOpApp values.reverse with
    | none => simpa [call] using bound
    | some pair =>
      obtain ⟨newEnv, body⟩ := pair
      by_cases zero : next.clock = 0
      · simp [call, zero]
      · have decrease : (decClock next).clock < state.clock := by
          simp only [decClock]
          omega
        have recursive := smallerClock newEnv (decClock next) body decrease
        have resultBound : (evaluate newEnv (decClock next) [body]).1.clock ≤ state.clock := by
          exact Nat.le_trans recursive (Nat.le_of_lt decrease)
        simpa [call, zero] using resultBound

/-- Dynamic evaluation preserves the incoming clock bound when declaration
evaluation at smaller clocks does. -/
theorem evaluate_eval_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (smallerClock : ∀ (newState : State C F) (decs : List FlatLang.Exp),
      newState.clock < state.clock → (evaluateDecs newState decs).1.clock ≤ newState.clock) :
    (evaluate env state [.app trace (.src .eval) args]).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state args.reverse)
  rw [evaluate]
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    cases decoded : doEval values.reverse next.evalConfig with
    | none => simpa [decoded] using bound
    | some payload =>
      obtain ⟨decs, config, returnValue⟩ := payload
      by_cases zero : next.clock = 0
      · simp [decoded, zero]
      · have decrease : (decClock { next with evalConfig := config }).clock < state.clock := by
          simp only [decClock]
          omega
        have recursive := smallerClock (decClock { next with evalConfig := config }) decs decrease
        have resultBound : (evaluateDecs (decClock { next with evalConfig := config }) decs).1.clock ≤ state.clock :=
          Nat.le_trans recursive (Nat.le_of_lt decrease)
        cases result : (evaluateDecs (decClock { next with evalConfig := config }) decs).2 <;>
          simpa [decoded, zero, result] using resultBound

/-- Thunk forcing preserves the clock bound when its generated application
does. The generated application has smaller expression weight. -/
theorem evaluate_force_clock_step {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (forceBodyClock : ∀ (next : State C F) (value : Value), next.clock ≤ state.clock →
      (evaluate ⟨[(Flapjack.Basis.Pure.MlString.ofString "f", value)]⟩ next
        [appUnit (.varLocal .none (Flapjack.Basis.Pure.MlString.ofString "f"))]).1.clock ≤ next.clock) :
    (evaluate env state [.app trace (.src (.thunkOp .forceThunk)) args]).1.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate env state args.reverse)
  rw [evaluate]
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    cases thunk : destThunk values next.refs with
    | badRef => simpa [thunk] using bound
    | notThunk => simpa [thunk] using bound
    | isThunk mode value =>
      cases mode with
      | evaluated => simpa [thunk] using bound
      | notEvaluated =>
        have recursive := forceBodyClock next value bound
        have resultBound := Nat.le_trans recursive bound
        generalize bodyRun : evaluate ⟨[(Flapjack.Basis.Pure.MlString.ofString "f", value)]⟩ next
          [appUnit (.varLocal .none (Flapjack.Basis.Pure.MlString.ofString "f"))] = output at *
        obtain ⟨last, output⟩ := output
        change last.clock ≤ state.clock at resultBound
        cases output with
        | err error => simpa [thunk, bodyRun] using resultBound
        | val newValues =>
          cases updated : updateThunk values last.refs newValues with
          | none => simpa [thunk, bodyRun, updated] using resultBound
          | some refs => simpa [thunk, bodyRun, updated] using resultBound

end Flapjack.Compiler.Backend.FlatSem
