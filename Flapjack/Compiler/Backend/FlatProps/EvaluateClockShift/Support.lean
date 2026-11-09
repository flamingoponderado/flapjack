module

public import Flapjack.Compiler.Backend.FlatProps.EvaluateList
public import Flapjack.Compiler.Backend.FlatProps.DoAppClock
public import Flapjack.Compiler.Backend.FlatProps.PatternMatch

@[expose] public section

/-! Shared evaluator equations used in the clock-extension and event proofs. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)
/-- Flapjack proof infrastructure: Clock changes preserve the row chosen by the evaluator. -/
theorem selectRowClock {C F : Type} (state : State C F)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (value noMatch : Value) (clock : Nat) :
    selectRow { state with clock := clock } rows value noMatch = selectRow state rows value noMatch := by
  simp only [selectRow, pmatchRows_ignoreClock]

/-- Flapjack proof infrastructure: Clock addition commutes with a positive clock decrement. -/
theorem decClockAdd {C F : Type} (state : State C F) (extra : Nat) (positive : state.clock ≠ 0) :
    decClock { state with clock := state.clock + extra } =
      { decClock state with clock := (decClock state).clock + extra } := by
  simp only [decClock]
  congr 1
  omega

/-- Flapjack proof infrastructure: Expose the matching case through the evaluator row-selection helper. -/
theorem matEquation {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (body : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    evaluate env state [.mat trace body rows] =
      match fixClock state (evaluate env state [body]) with
      | (next, .err error) => (next, .err error)
      | (next, .val values) => match selectRow next rows (@Flapjack.holHd Value ⟨unitValue⟩ values) bindExnV with
        | .error error => (next, .err error)
        | .ok (bindings, branch) => evaluate { env with v := bindings ++ env.v } next [branch] := by
  rw [evaluate]
  generalize fixClock state (evaluate env state [body]) = result
  obtain ⟨next, result⟩ := result
  cases result with
  | err error => rfl
  | val values =>
    simp only [headValue_eq_holHd]
    cases selectRow next rows (@Flapjack.holHd Value ⟨unitValue⟩ values) bindExnV <;> rfl

/-- Flapjack proof infrastructure: Expose the handler case through the evaluator row-selection helper. -/
theorem handleEquation {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (body : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    evaluate env state [.handle trace body rows] =
      match fixClock state (evaluate env state [body]) with
      | (next, .err (.raise value)) => match selectRow next rows value value with
        | .error error => (next, .err error)
        | .ok (bindings, branch) => evaluate { env with v := bindings ++ env.v } next [branch]
      | (next, result) => (next, result) := by
  rw [evaluate]
  generalize fixClock state (evaluate env state [body]) = result
  obtain ⟨next, result⟩ := result
  cases result with
  | val values => rfl
  | err error =>
    cases error with
    | abort abort => rfl
    | raise value =>
      dsimp only
      cases selectRow next rows value value <;> simp

/-- Flapjack proof infrastructure: The lifted primitive result commutes with clock addition. -/
theorem applyResultAddClock {C F : Type} (state : State C F) (op : FlatLang.Op)
    (values : List Value) (extra : Nat) :
    applyResult { state with clock := state.clock + extra } op values =
      ({ (applyResult state op values).1 with clock := (applyResult state op values).1.clock + extra },
        (applyResult state op values).2) := by
  cases run : doApp state op values with
  | none =>
    have shifted := doApp_addToClock_none state op values extra run
    simp [applyResult, run, shifted]
  | some pair =>
    obtain ⟨next, result⟩ := pair
    have shifted := doApp_addToClock state op values next result extra run
    cases result <;> simp [applyResult, run, shifted]

/-- Flapjack proof infrastructure: Expose the evaluator clause for non-special primitive operations. -/
theorem appOtherEquation {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (op : FlatLang.Op) (args : List FlatLang.Exp)
    (notCall : op ≠ .src .opapp) (notEval : op ≠ .src .eval)
    (notForce : op ≠ .src (.thunkOp .forceThunk)) :
    evaluate env state [.app trace op args] =
      match fixClock state (evaluate env state args.reverse) with
      | (next, .err error) => (next, .err error)
      | (next, .val values) => applyResult next op values.reverse := by
  rw [evaluate]
  generalize fixClock state (evaluate env state args.reverse) = result
  obtain ⟨next, result⟩ := result
  cases result with
  | err error => rfl
  | val values =>
    cases op with
    | src source => cases source <;> simp_all [applyResult]
    | globalVarAlloc n | globalVarInit n | globalVarLookup n | el n => rfl
    | tagLenEq n m => rfl
    | lenEq n => rfl
    | id => rfl


end Flapjack.Compiler.Backend.FlatProps
