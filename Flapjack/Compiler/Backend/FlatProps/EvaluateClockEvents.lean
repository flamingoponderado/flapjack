import Flapjack.Compiler.Backend.FlatProps.DoAppIO
import Flapjack.Compiler.Backend.FlatProps.EvaluateIO
import Flapjack.Compiler.Backend.FlatProps.EvaluateClockShift

/-! I/O-event monotonicity under clock extension for the faithful flat evaluator.
The private helpers assemble the mutual induction and have no separate HOL originals. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)
private def ClockObservation {C F α : Type} (extra : Nat)
    (small large : State C F × Result α Value) : Prop :=
  small.1.ffi.ioEvents <+: large.1.ffi.ioEvents ∧
    (small.2 ≠ .err (.abort .timeoutError) →
      large = ({ small.1 with clock := small.1.clock + extra }, small.2))

private theorem observationStep {C F α : Type} (extra : Nat) (bound : Nat)
    (small large : State C F × Result α Value)
    (cont : State C F → Result α Value → State C F)
    (observed : ClockObservation extra small large)
    (smallBound : small.1.clock ≤ bound)
    (monotone : ∀ state result, state.ffi.ioEvents <+: (cont state result).ffi.ioEvents)
    (timeoutStops : ∀ state, (cont state (.err (.abort .timeoutError))).ffi.ioEvents = state.ffi.ioEvents)
    (shifted : ∀ state result, state.clock ≤ bound → result ≠ .err (.abort .timeoutError) →
      (cont state result).ffi.ioEvents <+: (cont { state with clock := state.clock + extra } result).ffi.ioEvents) :
    (cont small.1 small.2).ffi.ioEvents <+: (cont large.1 large.2).ffi.ioEvents := by
  by_cases timedOut : small.2 = .err (.abort .timeoutError)
  · rw [timedOut, timeoutStops]
    exact observed.1.trans (monotone large.1 large.2)
  · have exactShift := observed.2 timedOut
    rw [exactShift]
    exact shifted small.1 small.2 smallBound timedOut

private theorem exprObservation {C F : Type} (extra : Nat) (env : Environment Value)
    (state : State C F) (es : List FlatLang.Exp)
    (events : (evaluate env state es).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } es).1.ffi.ioEvents) :
    ClockObservation extra (evaluate env state es) (evaluate env { state with clock := state.clock + extra } es) := by
  refine ⟨events, ?_⟩
  cases run : evaluate env state es with
  | mk next result =>
    intro safe
    exact (evaluate_addToClock extra).1 env state es next result ⟨run, safe⟩

private theorem fixObservation {C F α : Type} (extra : Nat) (state : State C F)
    (small large : State C F × Result α Value) (observed : ClockObservation extra small large) :
    ClockObservation extra (fixClock state small)
      (fixClock { state with clock := state.clock + extra } large) := by
  refine ⟨observed.1, ?_⟩
  intro safe
  have same := observed.2 safe
  rcases small with ⟨next, result⟩
  simp only at same
  rw [same]
  simp [fixClock, Nat.add_min_add_right]

private theorem evalConsEvents {C F : Type} (env : Environment Value) (state : State C F)
    (first : FlatLang.Exp) (rest : List FlatLang.Exp) (extra : Nat)
    (headIH : (evaluate env state [first]).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } [first]).1.ffi.ioEvents)
    (tailIH : ∀ middle : State C F, middle.clock ≤ state.clock →
      (evaluate env middle rest).1.ffi.ioEvents <+:
        (evaluate env { middle with clock := middle.clock + extra } rest).1.ffi.ioEvents) :
    (evaluate env state (first :: rest)).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } (first :: rest)).1.ffi.ioEvents := by
  cases head : evaluate env state [first] with
  | mk middle headResult =>
    have bound : middle.clock ≤ state.clock := by
      have bound := evaluate_clock_mutual.1 env state [first]
      simpa [head] using bound
    cases headResult with
    | err error =>
      by_cases timeout : error = .abort .timeoutError
      · subst error
        cases largeHead : evaluate env { state with clock := state.clock + extra } [first] with
        | mk middle' result' =>
          have events : middle.ffi.ioEvents <+: middle'.ffi.ioEvents := by simpa [head, largeHead] using headIH
          cases result' with
          | err error' => simpa [evaluate_cons, head, largeHead] using events
          | val values' =>
            have tail := (evaluate_ioEventsMono (C := C) (F := F)).1 env middle' rest
            cases largeTail : evaluate env middle' rest with
            | mk last result =>
              cases result <;> simpa [evaluate_cons, head, largeHead, largeTail] using events.trans tail
      · have safe : Result.err error ≠ (.err (.abort .timeoutError) : Result (List Value) Value) := by
          simpa using timeout
        have shifted := (evaluate_addToClock (C := C) (F := F) extra).1 env state [first] middle (.err error) ⟨head, safe⟩
        simp [evaluate_cons, head, shifted]
    | val values =>
      have shifted := (evaluate_addToClock (C := C) (F := F) extra).1 env state [first] middle (.val values)
        ⟨head, by simp⟩
      have tail := tailIH middle bound
      cases oldTail : evaluate env middle rest with
      | mk last result =>
        cases newTail : evaluate env { middle with clock := middle.clock + extra } rest with
        | mk last' result' =>
          cases result <;> cases result' <;>
            simpa [evaluate_cons, head, shifted, oldTail, newTail] using tail
private theorem evalIfEvents {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (cond yes no : FlatLang.Exp) (extra : Nat)
    (headIH : (evaluate env state [cond]).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } [cond]).1.ffi.ioEvents)
    (yesIH : ∀ middle : State C F, middle.clock ≤ state.clock →
      (evaluate env middle [yes]).1.ffi.ioEvents <+:
        (evaluate env { middle with clock := middle.clock + extra } [yes]).1.ffi.ioEvents)
    (noIH : ∀ middle : State C F, middle.clock ≤ state.clock →
      (evaluate env middle [no]).1.ffi.ioEvents <+:
        (evaluate env { middle with clock := middle.clock + extra } [no]).1.ffi.ioEvents) :
    (evaluate env state [.if_ trace cond yes no]).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } [.if_ trace cond yes no]).1.ffi.ioEvents := by
  let small := fixClock state (evaluate env state [cond])
  let large := fixClock { state with clock := state.clock + extra }
    (evaluate env { state with clock := state.clock + extra } [cond])
  let cont (middle : State C F) (result : Result (List Value) Value) : State C F :=
    match result with
    | .err _ => middle
    | .val values => match doIf (@Flapjack.holHd Value ⟨unitValue⟩ values) yes no with
      | none => middle
      | some branch => (evaluate env middle [branch]).1
  have observed : ClockObservation extra small large :=
    fixObservation extra state _ _ (exprObservation extra env state [cond] headIH)
  have bound : small.1.clock ≤ state.clock := fixClock_clock_le state _
  have monotone : ∀ middle result, middle.ffi.ioEvents <+: (cont middle result).ffi.ioEvents := by
    intro middle result
    cases result with
    | err _ => exact List.prefix_refl _
    | val values =>
      dsimp only [cont]
      cases selected : doIf (@Flapjack.holHd Value ⟨unitValue⟩ values) yes no with
      | none => exact List.prefix_refl _
      | some branch => exact (evaluate_ioEventsMono (C := C) (F := F)).1 env middle [branch]
  have stops : ∀ middle, (cont middle (.err (.abort .timeoutError))).ffi.ioEvents = middle.ffi.ioEvents := by
    intro middle
    rfl
  have shifted : ∀ middle result, middle.clock ≤ state.clock → result ≠ .err (.abort .timeoutError) →
      (cont middle result).ffi.ioEvents <+: (cont { middle with clock := middle.clock + extra } result).ffi.ioEvents := by
    intro middle result bound _
    cases result with
    | err _ => exact List.prefix_refl _
    | val values =>
      dsimp only [cont]
      cases selected : doIf (@Flapjack.holHd Value ⟨unitValue⟩ values) yes no with
      | none => exact List.prefix_refl _
      | some branch =>
        have choice := doIf_either_or _ yes no branch selected
        rcases choice with rfl | rfl
        · exact yesIH middle bound
        · exact noIH middle bound
  have composed := observationStep extra state.clock small large cont observed bound monotone stops shifted
  have stateEquation (s : State C F) : (evaluate env s [.if_ trace cond yes no]).1 =
      cont (fixClock s (evaluate env s [cond])).1 (fixClock s (evaluate env s [cond])).2 := by
    rw [evaluate_if_source]
    generalize fixClock s (evaluate env s [cond]) = pair
    obtain ⟨middle, result⟩ := pair
    cases result with
    | err error => rfl
    | val values =>
      dsimp only [cont]
      cases doIf (@Flapjack.holHd Value ⟨unitValue⟩ values) yes no <;> simp
  rw [stateEquation state, stateEquation { state with clock := state.clock + extra }]
  exact composed

private theorem evalLetEvents {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (name : Option Flapjack.AstHOL.VarN)
    (first body : FlatLang.Exp) (extra : Nat)
    (headIH : (evaluate env state [first]).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } [first]).1.ffi.ioEvents)
    (bodyIH : ∀ (newEnv : Environment Value) (middle : State C F), middle.clock ≤ state.clock →
      (evaluate newEnv middle [body]).1.ffi.ioEvents <+:
        (evaluate newEnv { middle with clock := middle.clock + extra } [body]).1.ffi.ioEvents) :
    (evaluate env state [.let_ trace name first body]).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } [.let_ trace name first body]).1.ffi.ioEvents := by
  let small := fixClock state (evaluate env state [first])
  let large := fixClock { state with clock := state.clock + extra }
    (evaluate env { state with clock := state.clock + extra } [first])
  let cont (middle : State C F) (result : Result (List Value) Value) : State C F :=
    match result with
    | .err _ => middle
    | .val values => (evaluate { env with v := match name with
        | none => env.v
        | some n => (n, @Flapjack.holHd Value ⟨unitValue⟩ values) :: env.v } middle [body]).1
  have observed : ClockObservation extra small large :=
    fixObservation extra state _ _ (exprObservation extra env state [first] headIH)
  have bound : small.1.clock ≤ state.clock := fixClock_clock_le state _
  have monotone : ∀ middle result, middle.ffi.ioEvents <+: (cont middle result).ffi.ioEvents := by
    intro middle result
    cases result with
    | err _ => exact List.prefix_refl _
    | val values => exact (evaluate_ioEventsMono (C := C) (F := F)).1 _ middle [body]
  have stops : ∀ middle, (cont middle (.err (.abort .timeoutError))).ffi.ioEvents = middle.ffi.ioEvents := by
    intro middle
    rfl
  have shifted : ∀ middle result, middle.clock ≤ state.clock → result ≠ .err (.abort .timeoutError) →
      (cont middle result).ffi.ioEvents <+: (cont { middle with clock := middle.clock + extra } result).ffi.ioEvents := by
    intro middle result bound _
    cases result with
    | err _ => exact List.prefix_refl _
    | val values => exact bodyIH _ middle bound
  have composed := observationStep extra state.clock small large cont observed bound monotone stops shifted
  have stateEquation (s : State C F) : (evaluate env s [.let_ trace name first body]).1 =
      cont (fixClock s (evaluate env s [first])).1 (fixClock s (evaluate env s [first])).2 := by
    rw [evaluate_let_source]
    generalize fixClock s (evaluate env s [first]) = pair
    obtain ⟨middle, result⟩ := pair
    cases result <;> rfl
  rw [stateEquation state, stateEquation { state with clock := state.clock + extra }]
  exact composed

private theorem evalMatEvents {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (body : FlatLang.Exp)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (extra : Nat)
    (headIH : (evaluate env state [body]).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } [body]).1.ffi.ioEvents)
    (rowIH : ∀ (middle : State C F) bindings branch, middle.clock ≤ state.clock →
      expWeight branch < rowsWeight rows →
      (evaluate { env with v := bindings ++ env.v } middle [branch]).1.ffi.ioEvents <+:
        (evaluate { env with v := bindings ++ env.v } { middle with clock := middle.clock + extra } [branch]).1.ffi.ioEvents) :
    (evaluate env state [.mat trace body rows]).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } [.mat trace body rows]).1.ffi.ioEvents := by
  let small := fixClock state (evaluate env state [body])
  let large := fixClock { state with clock := state.clock + extra }
    (evaluate env { state with clock := state.clock + extra } [body])
  let cont (middle : State C F) (result : Result (List Value) Value) : State C F :=
    match result with
    | .err _ => middle
    | .val values => match selectRow middle rows (@Flapjack.holHd Value ⟨unitValue⟩ values) bindExnV with
      | .error _ => middle
      | .ok (bindings, branch) => (evaluate { env with v := bindings ++ env.v } middle [branch]).1
  have observed : ClockObservation extra small large :=
    fixObservation extra state _ _ (exprObservation extra env state [body] headIH)
  have bound : small.1.clock ≤ state.clock := fixClock_clock_le state _
  have monotone : ∀ middle result, middle.ffi.ioEvents <+: (cont middle result).ffi.ioEvents := by
    intro middle result
    cases result with
    | err _ => exact List.prefix_refl _
    | val values =>
      dsimp only [cont]
      cases selected : selectRow middle rows (@Flapjack.holHd Value ⟨unitValue⟩ values) bindExnV with
      | error _ => exact List.prefix_refl _
      | ok pair =>
        obtain ⟨bindings, branch⟩ := pair
        exact (evaluate_ioEventsMono (C := C) (F := F)).1 _ middle [branch]
  have stops : ∀ middle, (cont middle (.err (.abort .timeoutError))).ffi.ioEvents = middle.ffi.ioEvents := by
    intro middle
    rfl
  have shifted : ∀ middle result, middle.clock ≤ state.clock → result ≠ .err (.abort .timeoutError) →
      (cont middle result).ffi.ioEvents <+: (cont { middle with clock := middle.clock + extra } result).ffi.ioEvents := by
    intro middle result bound _
    cases result with
    | err _ => exact List.prefix_refl _
    | val values =>
      dsimp only [cont]
      rw [selectRowClock middle rows (@Flapjack.holHd Value ⟨unitValue⟩ values) bindExnV (middle.clock + extra)]
      cases selected : selectRow middle rows (@Flapjack.holHd Value ⟨unitValue⟩ values) bindExnV with
      | error _ => exact List.prefix_refl _
      | ok pair =>
        obtain ⟨bindings, branch⟩ := pair
        exact rowIH middle bindings branch bound (selectRow_weight rows middle _ bindExnV bindings branch selected)
  have composed := observationStep extra state.clock small large cont observed bound monotone stops shifted
  have stateEquation (s : State C F) : (evaluate env s [.mat trace body rows]).1 =
      cont (fixClock s (evaluate env s [body])).1 (fixClock s (evaluate env s [body])).2 := by
    rw [matEquation]
    generalize fixClock s (evaluate env s [body]) = pair
    obtain ⟨middle, result⟩ := pair
    cases result with
    | err error => rfl
    | val values =>
      dsimp only [cont]
      cases selectRow middle rows (@Flapjack.holHd Value ⟨unitValue⟩ values) bindExnV <;> simp
  rw [stateEquation state, stateEquation { state with clock := state.clock + extra }]
  exact composed

private theorem evalHandleEvents {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (body : FlatLang.Exp)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (extra : Nat)
    (headIH : (evaluate env state [body]).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } [body]).1.ffi.ioEvents)
    (rowIH : ∀ (middle : State C F) bindings branch, middle.clock ≤ state.clock →
      expWeight branch < rowsWeight rows →
      (evaluate { env with v := bindings ++ env.v } middle [branch]).1.ffi.ioEvents <+:
        (evaluate { env with v := bindings ++ env.v } { middle with clock := middle.clock + extra } [branch]).1.ffi.ioEvents) :
    (evaluate env state [.handle trace body rows]).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } [.handle trace body rows]).1.ffi.ioEvents := by
  let small := fixClock state (evaluate env state [body])
  let large := fixClock { state with clock := state.clock + extra }
    (evaluate env { state with clock := state.clock + extra } [body])
  let cont (middle : State C F) (result : Result (List Value) Value) : State C F :=
    match result with
    | .err (.raise value) => match selectRow middle rows value value with
      | .error _ => middle
      | .ok (bindings, branch) => (evaluate { env with v := bindings ++ env.v } middle [branch]).1
    | _ => middle
  have observed : ClockObservation extra small large :=
    fixObservation extra state _ _ (exprObservation extra env state [body] headIH)
  have bound : small.1.clock ≤ state.clock := fixClock_clock_le state _
  have monotone : ∀ middle result, middle.ffi.ioEvents <+: (cont middle result).ffi.ioEvents := by
    intro middle result
    cases result with
    | val _ => exact List.prefix_refl _
    | err error =>
      cases error with
      | abort _ => exact List.prefix_refl _
      | raise value =>
        dsimp only [cont]
        cases selected : selectRow middle rows value value with
        | error _ => exact List.prefix_refl _
        | ok pair =>
          obtain ⟨bindings, branch⟩ := pair
          exact (evaluate_ioEventsMono (C := C) (F := F)).1 _ middle [branch]
  have stops : ∀ middle, (cont middle (.err (.abort .timeoutError))).ffi.ioEvents = middle.ffi.ioEvents := by
    intro middle
    rfl
  have shifted : ∀ middle result, middle.clock ≤ state.clock → result ≠ .err (.abort .timeoutError) →
      (cont middle result).ffi.ioEvents <+: (cont { middle with clock := middle.clock + extra } result).ffi.ioEvents := by
    intro middle result bound _
    cases result with
    | val _ => exact List.prefix_refl _
    | err error =>
      cases error with
      | abort _ => exact List.prefix_refl _
      | raise value =>
        dsimp only [cont]
        rw [selectRowClock middle rows value value (middle.clock + extra)]
        cases selected : selectRow middle rows value value with
        | error _ => exact List.prefix_refl _
        | ok pair =>
          obtain ⟨bindings, branch⟩ := pair
          exact rowIH middle bindings branch bound (selectRow_weight rows middle value value bindings branch selected)
  have composed := observationStep extra state.clock small large cont observed bound monotone stops shifted
  have stateEquation (s : State C F) : (evaluate env s [.handle trace body rows]).1 =
      cont (fixClock s (evaluate env s [body])).1 (fixClock s (evaluate env s [body])).2 := by
    rw [handleEquation]
    generalize fixClock s (evaluate env s [body]) = pair
    obtain ⟨middle, result⟩ := pair
    cases result with
    | val values => rfl
    | err error =>
      cases error with
      | abort _ => rfl
      | raise value =>
        dsimp only [cont]
        cases selectRow middle rows value value <;> simp
  rw [stateEquation state, stateEquation { state with clock := state.clock + extra }]
  exact composed

private theorem evalDecsEvents {C F : Type} (state : State C F) (d : FlatLang.Exp)
    (rest : List FlatLang.Exp) (extra : Nat)
    (headIH : (evaluate ⟨[]⟩ state [d]).1.ffi.ioEvents <+:
      (evaluate ⟨[]⟩ { state with clock := state.clock + extra } [d]).1.ffi.ioEvents)
    (tailIH : ∀ middle : State C F, middle.clock ≤ state.clock →
      (evaluateDecs middle rest).1.ffi.ioEvents <+:
        (evaluateDecs { middle with clock := middle.clock + extra } rest).1.ffi.ioEvents) :
    (evaluateDecs state (d :: rest)).1.ffi.ioEvents <+:
      (evaluateDecs { state with clock := state.clock + extra } (d :: rest)).1.ffi.ioEvents := by
  classical
  let small := fixClock state (evaluate ⟨[]⟩ state [d])
  let large := fixClock { state with clock := state.clock + extra }
    (evaluate ⟨[]⟩ { state with clock := state.clock + extra } [d])
  let cont (middle : State C F) (result : Result (List Value) Value) : State C F :=
    match result with
    | .err _ => middle
    | .val values => if values = [unitValue] then (evaluateDecs middle rest).1 else middle
  have observed : ClockObservation extra small large :=
    fixObservation extra state _ _ (exprObservation extra ⟨[]⟩ state [d] headIH)
  have bound : small.1.clock ≤ state.clock := fixClock_clock_le state _
  have monotone : ∀ middle result, middle.ffi.ioEvents <+: (cont middle result).ffi.ioEvents := by
    intro middle result
    cases result with
    | err _ => exact List.prefix_refl _
    | val values =>
      dsimp only [cont]
      split
      · exact (evaluate_ioEventsMono (C := C) (F := F)).2.2 middle rest
      · exact List.prefix_refl _
  have stops : ∀ middle, (cont middle (.err (.abort .timeoutError))).ffi.ioEvents = middle.ffi.ioEvents := by
    intro middle
    rfl
  have shifted : ∀ middle result, middle.clock ≤ state.clock → result ≠ .err (.abort .timeoutError) →
      (cont middle result).ffi.ioEvents <+: (cont { middle with clock := middle.clock + extra } result).ffi.ioEvents := by
    intro middle result bound _
    cases result with
    | err _ => exact List.prefix_refl _
    | val values =>
      dsimp only [cont]
      split
      · exact tailIH middle bound
      · exact List.prefix_refl _
  have composed := observationStep extra state.clock small large cont observed bound monotone stops shifted
  have stateEquation (s : State C F) : (evaluateDecs s (d :: rest)).1 =
      cont (fixClock s (evaluate ⟨[]⟩ s [d])).1 (fixClock s (evaluate ⟨[]⟩ s [d])).2 := by
    rw [(fixClock_evaluations ⟨[]⟩ s [d] d rest).1, evaluateDecs_cons, evaluateDec_source]
    generalize evaluate ⟨[]⟩ s [d] = pair
    obtain ⟨middle, result⟩ := pair
    cases result with
    | err error => rfl
    | val values => by_cases unit : values = [unitValue] <;> simp [cont, unit]
  rw [stateEquation state, stateEquation { state with clock := state.clock + extra }]
  exact composed

private theorem applyResultEvents {C F : Type} (state : State C F) (op : FlatLang.Op)
    (values : List Value) : state.ffi.ioEvents <+: (applyResult state op values).1.ffi.ioEvents := by
  cases run : doApp state op values with
  | none => simp [applyResult, run]
  | some pair =>
    obtain ⟨next, result⟩ := pair
    have events := doApp_ioEventsMono state op values next result run
    cases result <;> simpa [applyResult, run] using events

private theorem appOtherEvents {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (op : FlatLang.Op) (args : List FlatLang.Exp)
    (extra : Nat) (notCall : op ≠ .src .opapp) (notEval : op ≠ .src .eval)
    (notForce : op ≠ .src (.thunkOp .forceThunk))
    (argsIH : (evaluate env state args.reverse).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } args.reverse).1.ffi.ioEvents) :
    (evaluate env state [.app trace op args]).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } [.app trace op args]).1.ffi.ioEvents := by
  let small := fixClock state (evaluate env state args.reverse)
  let large := fixClock { state with clock := state.clock + extra }
    (evaluate env { state with clock := state.clock + extra } args.reverse)
  let cont (middle : State C F) (result : Result (List Value) Value) : State C F :=
    match result with
    | .err _ => middle
    | .val values => (applyResult middle op values.reverse).1
  have observed : ClockObservation extra small large :=
    fixObservation extra state _ _ (exprObservation extra env state args.reverse argsIH)
  have bound : small.1.clock ≤ state.clock := fixClock_clock_le state _
  have monotone : ∀ middle result, middle.ffi.ioEvents <+: (cont middle result).ffi.ioEvents := by
    intro middle result
    cases result with
    | err _ => exact List.prefix_refl _
    | val values => exact applyResultEvents middle op values.reverse
  have stops : ∀ middle, (cont middle (.err (.abort .timeoutError))).ffi.ioEvents = middle.ffi.ioEvents := by
    intro middle
    rfl
  have shifted : ∀ middle result, middle.clock ≤ state.clock → result ≠ .err (.abort .timeoutError) →
      (cont middle result).ffi.ioEvents <+: (cont { middle with clock := middle.clock + extra } result).ffi.ioEvents := by
    intro middle result _ _
    cases result with
    | err _ => exact List.prefix_refl _
    | val values =>
      dsimp only [cont]
      rw [applyResultAddClock middle op values.reverse extra]
      exact List.prefix_refl _
  have composed := observationStep extra state.clock small large cont observed bound monotone stops shifted
  have stateEquation (s : State C F) : (evaluate env s [.app trace op args]).1 =
      cont (fixClock s (evaluate env s args.reverse)).1 (fixClock s (evaluate env s args.reverse)).2 := by
    rw [appOtherEquation env s trace op args notCall notEval notForce]
    generalize fixClock s (evaluate env s args.reverse) = pair
    obtain ⟨middle, result⟩ := pair
    cases result <;> rfl
  rw [stateEquation state, stateEquation { state with clock := state.clock + extra }]
  exact composed

private theorem appCallEvents {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (args : List FlatLang.Exp) (extra : Nat)
    (argsIH : (evaluate env state args.reverse).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } args.reverse).1.ffi.ioEvents)
    (bodyIH : ∀ (env' : Environment Value) (s : State C F) (body : FlatLang.Exp),
      s.clock < state.clock → (evaluate env' s [body]).1.ffi.ioEvents <+:
        (evaluate env' { s with clock := s.clock + extra } [body]).1.ffi.ioEvents) :
    (evaluate env state [.app trace (.src .opapp) args]).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } [.app trace (.src .opapp) args]).1.ffi.ioEvents := by
  let small := fixClock state (evaluate env state args.reverse)
  let large := fixClock { state with clock := state.clock + extra }
    (evaluate env { state with clock := state.clock + extra } args.reverse)
  let cont (middle : State C F) (result : Result (List Value) Value) : State C F :=
    match result with
    | .err _ => middle
    | .val values => match doOpApp values.reverse with
      | none => middle
      | some (newEnv, body) => if middle.clock = 0 then middle else (evaluate newEnv (decClock middle) [body]).1
  have observed : ClockObservation extra small large :=
    fixObservation extra state _ _ (exprObservation extra env state args.reverse argsIH)
  have bound : small.1.clock ≤ state.clock := fixClock_clock_le state _
  have monotone : ∀ middle result, middle.ffi.ioEvents <+: (cont middle result).ffi.ioEvents := by
    intro middle result
    cases result with
    | err _ => exact List.prefix_refl _
    | val values =>
      dsimp only [cont]
      cases call : doOpApp values.reverse with
      | none => exact List.prefix_refl _
      | some pair =>
        obtain ⟨newEnv, body⟩ := pair
        simp only
        split
        · exact List.prefix_refl _
        · simpa [decClock] using (evaluate_ioEventsMono (C := C) (F := F)).1 newEnv (decClock middle) [body]
  have stops : ∀ middle, (cont middle (.err (.abort .timeoutError))).ffi.ioEvents = middle.ffi.ioEvents := by
    intro middle
    rfl
  have shifted : ∀ middle result, middle.clock ≤ state.clock → result ≠ .err (.abort .timeoutError) →
      (cont middle result).ffi.ioEvents <+: (cont { middle with clock := middle.clock + extra } result).ffi.ioEvents := by
    intro middle result bound _
    cases result with
    | err _ => exact List.prefix_refl _
    | val values =>
      dsimp only [cont]
      cases call : doOpApp values.reverse with
      | none => exact List.prefix_refl _
      | some pair =>
        obtain ⟨newEnv, body⟩ := pair
        simp only
        by_cases zero : middle.clock = 0
        · by_cases shiftedZero : middle.clock + extra = 0
          · have extraZero : extra = 0 := by omega
            simp [zero, extraZero]
          · have extraNonzero : extra ≠ 0 := by omega
            simpa [zero, extraNonzero, decClock] using
              (evaluate_ioEventsMono (C := C) (F := F)).1 newEnv (decClock { middle with clock := middle.clock + extra }) [body]
        · have decrease : (decClock middle).clock < state.clock := by simp [decClock]; omega
          have nonzero : middle.clock + extra ≠ 0 := by omega
          simpa only [zero, nonzero, ↓reduceIte, decClockAdd middle extra zero] using
            bodyIH newEnv (decClock middle) body decrease
  have composed := observationStep extra state.clock small large cont observed bound monotone stops shifted
  have stateEquation (s : State C F) : (evaluate env s [.app trace (.src .opapp) args]).1 =
      cont (fixClock s (evaluate env s args.reverse)).1 (fixClock s (evaluate env s args.reverse)).2 := by
    rw [evaluate_app_source]
    generalize fixClock s (evaluate env s args.reverse) = pair
    obtain ⟨middle, result⟩ := pair
    cases result with
    | err _ => rfl
    | val values =>
      dsimp only [cont]
      cases call : doOpApp values.reverse with
      | none => simp
      | some pair => obtain ⟨newEnv, body⟩ := pair; simp only; split <;> rfl
  rw [stateEquation state, stateEquation { state with clock := state.clock + extra }]
  exact composed

private theorem appEvalEvents {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (args : List FlatLang.Exp) (extra : Nat)
    (argsIH : (evaluate env state args.reverse).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } args.reverse).1.ffi.ioEvents)
    (decsIH : ∀ (s : State C F) (ds : List FlatLang.Exp),
      s.clock < state.clock → (evaluateDecs s ds).1.ffi.ioEvents <+:
        (evaluateDecs { s with clock := s.clock + extra } ds).1.ffi.ioEvents) :
    (evaluate env state [.app trace (.src .eval) args]).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } [.app trace (.src .eval) args]).1.ffi.ioEvents := by
  let small := fixClock state (evaluate env state args.reverse)
  let large := fixClock { state with clock := state.clock + extra }
    (evaluate env { state with clock := state.clock + extra } args.reverse)
  let cont (middle : State C F) (result : Result (List Value) Value) : State C F :=
    match result with
    | .err _ => middle
    | .val values => match doEval values.reverse middle.evalConfig with
      | none => middle
      | some (decs, config, _) =>
        if middle.clock = 0 then { middle with evalConfig := config }
        else (evaluateDecs (decClock { middle with evalConfig := config }) decs).1
  have observed : ClockObservation extra small large :=
    fixObservation extra state _ _ (exprObservation extra env state args.reverse argsIH)
  have bound : small.1.clock ≤ state.clock := fixClock_clock_le state _
  have monotone : ∀ middle result, middle.ffi.ioEvents <+: (cont middle result).ffi.ioEvents := by
    intro middle result
    cases result with
    | err _ => exact List.prefix_refl _
    | val values =>
      dsimp only [cont]
      cases decoded : doEval values.reverse middle.evalConfig with
      | none => exact List.prefix_refl _
      | some payload =>
        obtain ⟨decs, config, result⟩ := payload
        simp only
        split
        · exact List.prefix_refl _
        · simpa [decClock] using (evaluate_ioEventsMono (C := C) (F := F)).2.2
            (decClock { middle with evalConfig := config }) decs
  have stops : ∀ middle, (cont middle (.err (.abort .timeoutError))).ffi.ioEvents = middle.ffi.ioEvents := by
    intro middle
    rfl
  have shifted : ∀ middle result, middle.clock ≤ state.clock → result ≠ .err (.abort .timeoutError) →
      (cont middle result).ffi.ioEvents <+: (cont { middle with clock := middle.clock + extra } result).ffi.ioEvents := by
    intro middle result bound _
    cases result with
    | err _ => exact List.prefix_refl _
    | val values =>
      dsimp only [cont]
      cases decoded : doEval values.reverse middle.evalConfig with
      | none => exact List.prefix_refl _
      | some payload =>
        obtain ⟨decs, config, result⟩ := payload
        by_cases zero : middle.clock = 0
        · by_cases shiftedZero : middle.clock + extra = 0
          · have extraZero : extra = 0 := by omega
            simp [zero, extraZero]
          · have extraNonzero : extra ≠ 0 := by omega
            simpa [zero, extraNonzero, decClock] using
              (evaluate_ioEventsMono (C := C) (F := F)).2.2
                (decClock { middle with clock := middle.clock + extra, evalConfig := config }) decs
        · have decrease : (decClock { middle with evalConfig := config }).clock < state.clock := by simp [decClock]; omega
          have nonzero : middle.clock + extra ≠ 0 := by omega
          simpa only [zero, nonzero, ↓reduceIte, decClockAdd { middle with evalConfig := config } extra zero] using
            decsIH (decClock { middle with evalConfig := config }) decs decrease
  have composed := observationStep extra state.clock small large cont observed bound monotone stops shifted
  have stateEquation (s : State C F) : (evaluate env s [.app trace (.src .eval) args]).1 =
      cont (fixClock s (evaluate env s args.reverse)).1 (fixClock s (evaluate env s args.reverse)).2 := by
    rw [evaluate_app_source]
    generalize fixClock s (evaluate env s args.reverse) = pair
    obtain ⟨middle, result⟩ := pair
    cases result with
    | err _ => rfl
    | val values =>
      dsimp only [cont]
      cases decoded : doEval values.reverse middle.evalConfig with
      | none => rfl
      | some payload =>
        obtain ⟨decs, config, result⟩ := payload
        simp only
        split
        · rfl
        · cases evaluateDecs (decClock { middle with evalConfig := config }) decs with
          | mk last error => cases error <;> rfl
  rw [stateEquation state, stateEquation { state with clock := state.clock + extra }]
  exact composed

private theorem appForceEvents {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (args : List FlatLang.Exp) (extra : Nat)
    (argsIH : (evaluate env state args.reverse).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } args.reverse).1.ffi.ioEvents)
    (forceIH : ∀ (s : State C F) (value : Value), s.clock ≤ state.clock →
      (evaluate ⟨[(Flapjack.Basis.Pure.MlString.ofString "f", value)]⟩ s
        [appUnit (.varLocal .none (Flapjack.Basis.Pure.MlString.ofString "f"))]).1.ffi.ioEvents <+:
      (evaluate ⟨[(Flapjack.Basis.Pure.MlString.ofString "f", value)]⟩ { s with clock := s.clock + extra }
        [appUnit (.varLocal .none (Flapjack.Basis.Pure.MlString.ofString "f"))]).1.ffi.ioEvents) :
    (evaluate env state [.app trace (.src (.thunkOp .forceThunk)) args]).1.ffi.ioEvents <+:
      (evaluate env { state with clock := state.clock + extra } [.app trace (.src (.thunkOp .forceThunk)) args]).1.ffi.ioEvents := by
  let small := fixClock state (evaluate env state args.reverse)
  let large := fixClock { state with clock := state.clock + extra }
    (evaluate env { state with clock := state.clock + extra } args.reverse)
  let cont (middle : State C F) (result : Result (List Value) Value) : State C F :=
    match result with
    | .err _ => middle
    | .val values => match destThunk values middle.refs with
      | .isThunk .notEvaluated value =>
        let name := Flapjack.Basis.Pure.MlString.ofString "f"
        (evaluate ⟨[(name, value)]⟩ middle [appUnit (.varLocal .none name)]).1
      | _ => middle
  have observed : ClockObservation extra small large :=
    fixObservation extra state _ _ (exprObservation extra env state args.reverse argsIH)
  have bound : small.1.clock ≤ state.clock := fixClock_clock_le state _
  have monotone : ∀ middle result, middle.ffi.ioEvents <+: (cont middle result).ffi.ioEvents := by
    intro middle result
    cases result with
    | err _ => exact List.prefix_refl _
    | val values =>
      dsimp only [cont]
      cases dest : destThunk values middle.refs with
      | badRef | notThunk => exact List.prefix_refl _
      | isThunk mode value =>
        cases mode with
        | evaluated => exact List.prefix_refl _
        | notEvaluated => exact (evaluate_ioEventsMono (C := C) (F := F)).1 _ _ _
  have stops : ∀ middle, (cont middle (.err (.abort .timeoutError))).ffi.ioEvents = middle.ffi.ioEvents := by
    intro middle
    rfl
  have shifted : ∀ middle result, middle.clock ≤ state.clock → result ≠ .err (.abort .timeoutError) →
      (cont middle result).ffi.ioEvents <+: (cont { middle with clock := middle.clock + extra } result).ffi.ioEvents := by
    intro middle result bound _
    cases result with
    | err _ => exact List.prefix_refl _
    | val values =>
      dsimp only [cont]
      cases dest : destThunk values middle.refs with
      | badRef | notThunk => exact List.prefix_refl _
      | isThunk mode value =>
        cases mode with
        | evaluated => exact List.prefix_refl _
        | notEvaluated => exact forceIH middle value bound
  have composed := observationStep extra state.clock small large cont observed bound monotone stops shifted
  have stateEquation (s : State C F) : (evaluate env s [.app trace (.src (.thunkOp .forceThunk)) args]).1.ffi.ioEvents =
      (cont (fixClock s (evaluate env s args.reverse)).1 (fixClock s (evaluate env s args.reverse)).2).ffi.ioEvents := by
    rw [evaluate_app_source]
    generalize fixClock s (evaluate env s args.reverse) = pair
    obtain ⟨middle, result⟩ := pair
    cases result with
    | err _ => rfl
    | val values =>
      dsimp only [cont]
      cases dest : destThunk values middle.refs with
      | badRef | notThunk => rfl
      | isThunk mode value =>
        cases mode with
        | evaluated => rfl
        | notEvaluated =>
          simp only
          cases bodyRun : evaluate ⟨[(Flapjack.Basis.Pure.MlString.ofString "f", value)]⟩ middle
              [appUnit (.varLocal .none (Flapjack.Basis.Pure.MlString.ofString "f"))] with
          | mk last result =>
            cases result with
            | err error => simp
            | val values' => cases updated : updateThunk values last.refs values' <;> simp [updated]
  rw [stateEquation state, stateEquation { state with clock := state.clock + extra }]
  exact composed

private def exprEvents {C F : Type} (extra : Nat) (env : Environment Value)
    (state : State C F) (es : List FlatLang.Exp) : Prop :=
  (evaluate env state es).1.ffi.ioEvents <+:
    (evaluate env { state with clock := state.clock + extra } es).1.ffi.ioEvents
private def decsEvents {C F : Type} (extra : Nat) (state : State C F) (ds : List FlatLang.Exp) : Prop :=
  (evaluateDecs state ds).1.ffi.ioEvents <+:
    (evaluateDecs { state with clock := state.clock + extra } ds).1.ffi.ioEvents

private theorem exprDecsEvents {C F : Type} (extra : Nat) :
    (∀ (env : Environment Value) (state : State C F) es, exprEvents extra env state es) ∧
    (∀ (state : State C F) ds, decsEvents extra state ds) := by
  apply flatEvaluateMeasureRec
  · intro env state es exprIH smallerE decIH smallerD
    cases es with
    | nil => simp [exprEvents, evaluate_nil_source]
    | cons first rest =>
      cases rest with
      | nil =>
        change (evaluate env state [first]).1.ffi.ioEvents <+:
          (evaluate env { state with clock := state.clock + extra } [first]).1.ffi.ioEvents
        cases first with
        | lit trace literal => simp [evaluate_lit_source]
        | fn trace name body => simp [evaluate_fn_source]
        | varLocal trace name => rw [evaluate_varLocal_source, evaluate_varLocal_source]; cases env.v.lookup name <;> simp
        | raise trace body =>
          have ih := exprIH env state [body] (by omega) (by simp only [expsWeight, expWeight]; omega)
          change (evaluate env state [body]).1.ffi.ioEvents <+:
            (evaluate env { state with clock := state.clock + extra } [body]).1.ffi.ioEvents at ih
          rw [evaluate_raise_source, evaluate_raise_source]
          cases leftRun : evaluate env state [body] with
          | mk left lr => cases lr <;> cases rightRun : evaluate env { state with clock := state.clock + extra } [body] with
            | mk right rr => cases rr <;> simpa [leftRun, rightRun] using ih
        | con trace constructor args =>
          have ih := exprIH env state args.reverse (by omega) (by rw [expsWeight_reverse]; simp only [expsWeight, expWeight]; omega)
          change (evaluate env state args.reverse).1.ffi.ioEvents <+:
            (evaluate env { state with clock := state.clock + extra } args.reverse).1.ffi.ioEvents at ih
          rw [evaluate_con_source, evaluate_con_source]
          cases leftRun : evaluate env state args.reverse with
          | mk left lr => cases lr <;> cases rightRun : evaluate env { state with clock := state.clock + extra } args.reverse with
            | mk right rr => cases rr <;> simpa [leftRun, rightRun] using ih
        | letrec trace funs body =>
          rw [evaluate_letrec_source, evaluate_letrec_source]
          split
          · exact exprIH _ state [body] (by omega) (by simp only [expsWeight, expWeight]; omega)
          · simp
        | if_ trace condition yes no =>
          apply evalIfEvents env state trace condition yes no extra
          · exact exprIH env state [condition] (by omega) (by simp only [expsWeight, expWeight]; omega)
          · intro middle bound
            exact exprIH env middle [yes] bound (by simp only [expsWeight, expWeight]; omega)
          · intro middle bound
            exact exprIH env middle [no] bound (by simp only [expsWeight, expWeight]; omega)
        | let_ trace name first body =>
          apply evalLetEvents env state trace name first body extra
          · exact exprIH env state [first] (by omega) (by simp only [expsWeight, expWeight]; omega)
          · intro newEnv middle bound
            exact exprIH newEnv middle [body] bound (by simp only [expsWeight, expWeight]; omega)
        | mat trace body rows =>
          apply evalMatEvents env state trace body rows extra
          · exact exprIH env state [body] (by omega) (by simp only [expsWeight, expWeight]; omega)
          · intro middle bindings branch bound weight
            exact exprIH _ middle [branch] bound (by simp only [expsWeight, expWeight]; omega)
        | handle trace body rows =>
          apply evalHandleEvents env state trace body rows extra
          · exact exprIH env state [body] (by omega) (by simp only [expsWeight, expWeight]; omega)
          · intro middle bindings branch bound weight
            exact exprIH _ middle [branch] bound (by simp only [expsWeight, expWeight]; omega)
        | app trace op args =>
          have argsIH := exprIH env state args.reverse (by omega) (by
            rw [expsWeight_reverse]; simp only [expsWeight, expWeight]; omega)
          by_cases call : op = .src .opapp
          · subst op
            apply appCallEvents env state trace args extra argsIH
            intro env' s body smaller
            exact smallerE env' s [body] smaller
          · by_cases dynamic : op = .src .eval
            · subst op
              apply appEvalEvents env state trace args extra argsIH
              intro s ds smaller
              exact smallerD s ds smaller
            · by_cases force : op = .src (.thunkOp .forceThunk)
              · subst op
                apply appForceEvents env state trace args extra argsIH
                intro s value hclock
                apply exprIH _ s _ hclock
                have weight := appUnit_force_weight trace args
                simp only [expsWeight]
                omega
              · exact appOtherEvents env state trace op args extra call dynamic force argsIH
      | cons second rest =>
        change (evaluate env state (first :: second :: rest)).1.ffi.ioEvents <+:
          (evaluate env { state with clock := state.clock + extra } (first :: second :: rest)).1.ffi.ioEvents
        apply evalConsEvents env state first (second :: rest) extra
        · apply exprIH env state [first] (by omega)
          simp only [expsWeight]; have := expWeight_pos second; omega
        · intro middle bound
          apply exprIH env middle (second :: rest) bound
          simp only [expsWeight]; omega
  · intro state ds exprIH smallerE decIH smallerD
    cases ds with
    | nil => simp [decsEvents, evaluateDecs_nil_source]
    | cons first rest =>
      change (evaluateDecs state (first :: rest)).1.ffi.ioEvents <+:
        (evaluateDecs { state with clock := state.clock + extra } (first :: rest)).1.ffi.ioEvents
      apply evalDecsEvents state first rest extra
      · exact exprIH ⟨[]⟩ state [first] (by omega) (by simp only [expsWeight]; omega)
      · intro middle bound
        apply decIH middle rest bound
        simp only [expsWeight]; have := expWeight_pos first; omega

/-- Adding clock preserves the event prefix for expressions and declarations, including timeouts. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_add_to_clock_io_events_mono"]
theorem evaluate_addToClock_ioEventsMono {C F : Type} (extra : Nat) :
    (∀ (env : Environment Value) (state : State C F) (es : List FlatLang.Exp),
      (evaluate env state es).1.ffi.ioEvents <+:
        (evaluate env { state with clock := state.clock + extra } es).1.ffi.ioEvents) ∧
    (∀ (state : State C F) (d : FlatLang.Exp),
      (evaluateDec state d).1.ffi.ioEvents <+:
        (evaluateDec { state with clock := state.clock + extra } d).1.ffi.ioEvents) ∧
    (∀ (state : State C F) (ds : List FlatLang.Exp),
      (evaluateDecs state ds).1.ffi.ioEvents <+:
        (evaluateDecs { state with clock := state.clock + extra } ds).1.ffi.ioEvents) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (exprDecsEvents extra).1
  · intro state d
    have events := (exprDecsEvents (C := C) (F := F) extra).1 ⟨[]⟩ state [d]
    change (evaluate ⟨[]⟩ state [d]).1.ffi.ioEvents <+:
      (evaluate ⟨[]⟩ { state with clock := state.clock + extra } [d]).1.ffi.ioEvents at events
    rw [evaluateDec_source, evaluateDec_source]
    cases leftRun : evaluate ⟨[]⟩ state [d] with
    | mk left lr => cases lr <;> cases rightRun : evaluate ⟨[]⟩ { state with clock := state.clock + extra } [d] with
      | mk right rr => cases rr <;> simp_all [apply_ite]
  · exact (exprDecsEvents extra).2

/-- Increasing clock extends the event trace of a declaration. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_dec_add_to_clock_io_events_mono"]
theorem evaluateDec_addToClock_ioEventsMono {C F : Type} :
    ∀ (d : FlatLang.Exp) (state : State C F) (extra : Nat),
      (evaluateDec state d).1.ffi.ioEvents <+:
        (evaluateDec { state with clock := state.clock + extra } d).1.ffi.ioEvents := by
  intro d state extra
  exact (evaluate_addToClock_ioEventsMono extra).2.1 state d

/-- Increasing clock extends the event trace of a declaration list. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_decs_add_to_clock_io_events_mono"]
theorem evaluateDecs_addToClock_ioEventsMono {C F : Type} :
    ∀ (ds : List FlatLang.Exp) (state : State C F) (extra : Nat),
      (evaluateDecs state ds).1.ffi.ioEvents <+:
        (evaluateDecs { state with clock := state.clock + extra } ds).1.ffi.ioEvents := by
  intro ds state extra
  exact (evaluate_addToClock_ioEventsMono extra).2.2 state ds

/-- Explicit evaluation results preserve the event prefix under clock extension. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_decs_add_to_clock_io_events_mono_alt"]
theorem evaluateDecs_addToClock_ioEventsMono_alt {C F : Type} (s : State C F) (ds : List FlatLang.Exp)
    (s1 : State C F) (res : Option (ErrorResult Value)) (extra : Nat)
    (s2 : State C F) (res2 : Option (ErrorResult Value))
    (premises : evaluateDecs s ds = (s1, res) ∧
      evaluateDecs { s with clock := s.clock + extra } ds = (s2, res2)) :
    s1.ffi.ioEvents <+: s2.ffi.ioEvents := by
  simpa [premises.1, premises.2] using evaluateDecs_addToClock_ioEventsMono ds s extra

end Flapjack.Compiler.Backend.FlatProps
