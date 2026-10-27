import Flapjack.EvaluateProps.ClockIoExpr

/-! Prerequisites for the application case of the source clock-and-I/O proof.
The complete application case is assembled in ClockIoFull; source/carrier review remains open. -/
namespace Flapjack.EvaluateProps
open Flapjack.EvaluateHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

/-- Flapjack helper: a clock-checked recursive function call preserves the invariant. -/
theorem clockIo_checkedCall {σ : Type} (st : State σ) (env : SemEnv Value) (body : AstHOL.Exp)
    (ih : st.clock ≠ 0 → isClockIoMono (fun state => evaluate state env [body]) (decClock st)) :
    isClockIoMono (fun state => if state.clock = 0 then timeoutError state
      else evaluate (decClock state) env [body]) st := by
  apply isClockIoMono_check (fun state => evaluate (decClock state) env [body]) st
  intro nonzero
  simpa only [decIncClock] using ih nonzero

/-- Flapjack helper: a successful thunk update preserves the store length. -/
theorem updateThunk_length (targets values : List Value) (store updated : Store Value)
    (h : updateThunk targets store values = some updated) : store.length = updated.length := by
  unfold updateThunk at h
  repeat' first | split at h | simp_all
  all_goals exact (storeAssign_length _ _ _ _ (by assumption)).symm

/-- Flapjack helper: committing a thunk result preserves the invariant. -/
theorem clockIo_updateThunk {σ : Type} (st : State σ) (targets values : List Value) :
    isClockIoMono (fun state => match updateThunk targets state.refs values with
      | none => typeError state
      | some refs => ({ state with refs }, Result.val (β := Value) values)) st := by
  cases hupdate : updateThunk targets st.refs values with
  | none => simp [isClockIoMono, hupdate, typeError, ioEventsMonoHOL]
  | some refs =>
    have length := updateThunk_length targets values st.refs refs hupdate
    simp [isClockIoMono, hupdate, ioEventsMonoHOL, length]

/-- Flapjack helper: decoding a dynamic evaluation request only updates Eval bookkeeping. -/
theorem clockIo_doEvalRes {σ β : Type} (st : State σ) (values : List Value) :
    isClockIoMono (fun state => doEvalRes (β := β) values state) st := by
  cases heval : doEval values st.evalState with
  | none => simp [isClockIoMono, doEvalRes, heval, ioEventsMonoHOL]
  | some output =>
    rcases output with ⟨env, decs, evalState⟩
    simp [isClockIoMono, doEvalRes, heval, ioEventsMonoHOL]

/-- Flapjack helper: restoring Eval generation on an exception preserves the invariant. -/
theorem clockIo_resetRaise {σ : Type} (st : State σ) (prior : Option EvalState) (value : Value) :
    isClockIoMono (fun state =>
      ({ state with evalState := resetEnvGeneration prior state.evalState },
        Result.err (α := List Value) (.raise value))) st := by
  simp [isClockIoMono, ioEventsMonoHOL]

/-- Flapjack helper: declaring a dynamic environment only changes Eval bookkeeping. -/
theorem clockIo_declareEnv {σ : Type} (st : State σ) (prior : Option EvalState)
    (evalEnv newEnv : SemEnv Value) :
    isClockIoMono (fun state => match declareEnv state.evalState (extendDecEnv newEnv evalEnv) with
      | none => typeError state
      | some (value, evalState) =>
        ({ state with evalState := resetEnvGeneration prior evalState }, Result.val (β := Value) [value])) st := by
  cases hdecl : declareEnv st.evalState (extendDecEnv newEnv evalEnv) with
  | none => simp [isClockIoMono, hdecl, typeError, ioEventsMonoHOL]
  | some output =>
    rcases output with ⟨value, evalState⟩
    simp [isClockIoMono, hdecl, ioEventsMonoHOL]

/-- Flapjack helper: clock-check a computation already proved at the decremented clock. -/
theorem clockIo_checked {σ α β : Type} (st : State σ) (f : State σ → State σ × Result α β)
    (ih : st.clock ≠ 0 → isClockIoMono f (decClock st)) :
    isClockIoMono (fun state => if state.clock = 0 then (state, .err (.abort .timeoutError))
      else f (decClock state)) st := by
  apply isClockIoMono_check (fun state => f (decClock state)) st
  intro nonzero
  simpa only [decIncClock] using ih nonzero

/-- Flapjack helper: preserve a thunk evaluation invariant while committing its result. -/
theorem clockIo_thunkResult {σ : Type} (st : State σ) (targets : List Value)
    (f : State σ → State σ × Result (List Value) Value) (ih : isClockIoMono f st) :
    isClockIoMono (fun state => let (next, result) := f state; match result with
      | .err error => (next, .err error)
      | .val values => match updateThunk targets next.refs values with
        | none => typeError next
        | some refs => ({ next with refs }, .val values)) st := by
  let continuation : Result (List Value) Value → State σ → State σ × Result (List Value) Value :=
    fun result state => match result with
      | .err error => (state, .err error)
      | .val values => match updateThunk targets state.refs values with
        | none => typeError state
        | some refs => ({ state with refs }, .val values)
  have hcont : ∀ next result, f st = (next, result) → isClockIoMono (continuation result) next := by
    intro next result _
    cases result with
    | err error => exact isClockIoMono_err (α := List Value) next error
    | val values => exact clockIo_updateThunk next targets values
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    rfl
  exact isClockIoMono_bind f continuation st ⟨ih, hcont, htimeout⟩

/-- Flapjack helper for the force branch of application. -/
theorem clockIo_force {σ : Type} (st : State σ) (values : List Value)
    (ih : ∀ thunk callEnv body,
      destThunk values st.refs = .isThunk .notEvaluated thunk →
      doOpApp [thunk, .conv none []] = some (callEnv, body) → st.clock ≠ 0 →
      isClockIoMono (fun state => evaluate state callEnv [body]) (decClock st)) :
    isClockIoMono (fun state => match destThunk values state.refs with
      | .badRef | .notThunk => typeError state
      | .isThunk .evaluated value => (state, .val [value])
      | .isThunk .notEvaluated thunk => match doOpApp [thunk, .conv none []] with
        | none => typeError state
        | some (callEnv, body) =>
          if state.clock = 0 then timeoutError state else
          let next := evaluate (decClock state) callEnv [body]
          match next.2 with
          | .err error => (next.1, .err error)
          | .val newValues => match updateThunk values next.1.refs newValues with
            | none => typeError next.1
            | some refs => ({ next.1 with refs }, .val newValues)) st := by
  let accessor : State σ → DestThunkResult := fun state => destThunk values state.refs
  let choose : DestThunkResult → State σ → State σ × Result (List Value) Value := fun choice state =>
    match choice with
    | .badRef | .notThunk => typeError state
    | .isThunk .evaluated value => (state, .val [value])
    | .isThunk .notEvaluated thunk => match doOpApp [thunk, .conv none []] with
      | none => typeError state
      | some (callEnv, body) =>
        if state.clock = 0 then timeoutError state else
        let next := evaluate (decClock state) callEnv [body]
        match next.2 with
        | .err error => (next.1, .err error)
        | .val newValues => match updateThunk values next.1.refs newValues with
          | none => typeError next.1
          | some refs => ({ next.1 with refs }, .val newValues)
  have fixed : isClockIoMono (fun state => choose (accessor st) state) st := by
    cases hd : destThunk values st.refs with
    | badRef => simpa only [accessor, hd, choose, typeError] using isClockIoMono_err (α := List Value) st (.abort .typeError)
    | notThunk => simpa only [accessor, hd, choose, typeError] using isClockIoMono_err (α := List Value) st (.abort .typeError)
    | isThunk mode thunk =>
      cases mode with
      | evaluated => simpa only [accessor, hd, choose] using isClockIoMono_return (β := Value) st [thunk]
      | notEvaluated =>
        cases happ : doOpApp [thunk, .conv none []] with
        | none => simpa only [accessor, hd, choose, happ, typeError] using isClockIoMono_err (α := List Value) st (.abort .typeError)
        | some call =>
          rcases call with ⟨callEnv, body⟩
          let f : State σ → State σ × Result (List Value) Value := fun state =>
            let next := evaluate state callEnv [body]
            match next.2 with
            | .err error => (next.1, .err error)
            | .val newValues => match updateThunk values next.1.refs newValues with
              | none => typeError next.1
              | some refs => ({ next.1 with refs }, .val newValues)
          have checked := clockIo_checked st f (by
            intro nonzero
            have base := clockIo_thunkResult (decClock st) values
              (fun state => evaluate state callEnv [body]) (ih thunk callEnv body hd happ nonzero)
            have fnEq : (fun state => let (next, result) := evaluate state callEnv [body]; match result with
                | .err error => (next, .err error)
                | .val newValues => match updateThunk values next.refs newValues with
                  | none => typeError next
                  | some refs => ({ next with refs }, .val newValues)) = f := by
              funext state
              dsimp only [f]
            rw [fnEq] at base
            exact base)
          simpa only [accessor, hd, choose, happ, f, timeoutError] using checked
  have independent : ∀ state clock, accessor { state with clock } = accessor state := by
    intro state clock
    rfl
  have result := isClockIoMono_accSafe accessor st .badRef choose ⟨independent, Classical.em _, fixed⟩
  exact result

/-- Flapjack helper: finish dynamic declarations without changing the invariant. -/
theorem clockIo_finishEval {σ : Type} (st : State σ) (prior : Option EvalState) (evalEnv : SemEnv Value)
    (f : State σ → State σ × Result (SemEnv Value) Value) (ih : isClockIoMono f st) :
    isClockIoMono (fun state => let (next, result) := f state; match result with
      | .val newEnv => match declareEnv next.evalState (extendDecEnv newEnv evalEnv) with
        | none => typeError next
        | some (value, evalState) =>
          ({ next with evalState := resetEnvGeneration prior evalState }, .val [value])
      | .err (.abort error) => (next, .err (.abort error))
      | .err (.raise value) =>
        ({ next with evalState := resetEnvGeneration prior next.evalState }, .err (.raise value))) st := by
  let continuation : Result (SemEnv Value) Value → State σ → State σ × Result (List Value) Value :=
    fun result state => match result with
      | .val newEnv => match declareEnv state.evalState (extendDecEnv newEnv evalEnv) with
        | none => typeError state
        | some (value, evalState) =>
          ({ state with evalState := resetEnvGeneration prior evalState }, .val [value])
      | .err (.abort error) => (state, .err (.abort error))
      | .err (.raise value) =>
        ({ state with evalState := resetEnvGeneration prior state.evalState }, .err (.raise value))
  have hcont : ∀ next result, f st = (next, result) → isClockIoMono (continuation result) next := by
    intro next result _
    cases result with
    | val newEnv => exact clockIo_declareEnv next prior evalEnv newEnv
    | err error =>
      cases error with
      | abort error => exact isClockIoMono_err (α := List Value) next (.abort error)
      | raise value => exact clockIo_resetRaise next prior value
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    rfl
  exact isClockIoMono_bind f continuation st ⟨ih, hcont, htimeout⟩

/-- Flapjack helper for the dynamic Eval operation. -/
theorem clockIo_evalOperation {σ : Type} (st : State σ) (values : List Value)
    (ih : ∀ decoded evalEnv decs, doEvalRes (β := Value) values st = (decoded, .val (evalEnv, decs)) →
      decoded.clock ≠ 0 → isClockIoMono (fun state => evaluateDecs state evalEnv decs) (decClock decoded)) :
    isClockIoMono (fun state =>
      let decoded := fixClock state (doEvalRes (β := Value) values state)
      match decoded.2 with
      | .err error => (decoded.1, .err error)
      | .val (evalEnv, decs) =>
        if decoded.1.clock = 0 then timeoutError decoded.1 else
        let next := fixClock (decClock decoded.1) (evaluateDecs (decClock decoded.1) evalEnv decs)
        match next.2 with
        | .val newEnv => match declareEnv next.1.evalState (extendDecEnv newEnv evalEnv) with
          | none => typeError next.1
          | some (value, evalState) =>
            ({ next.1 with evalState := resetEnvGeneration state.evalState evalState }, .val [value])
        | .err (.abort error) => (next.1, .err (.abort error))
        | .err error => ({ next.1 with evalState := resetEnvGeneration state.evalState next.1.evalState }, .err error)) st := by
  let accessor : State σ → Option EvalState := fun state => state.evalState
  let choose : Option EvalState → State σ → State σ × Result (List Value) Value := fun prior state =>
    let decoded := doEvalRes (β := Value) values state
    match decoded.2 with
    | .err error => (decoded.1, .err error)
    | .val (evalEnv, decs) =>
      if decoded.1.clock = 0 then timeoutError decoded.1 else
      let next := evaluateDecs (decClock decoded.1) evalEnv decs
      match next.2 with
      | .val newEnv => match declareEnv next.1.evalState (extendDecEnv newEnv evalEnv) with
        | none => typeError next.1
        | some (value, evalState) =>
          ({ next.1 with evalState := resetEnvGeneration prior evalState }, .val [value])
      | .err (.abort error) => (next.1, .err (.abort error))
      | .err error => ({ next.1 with evalState := resetEnvGeneration prior next.1.evalState }, .err error)
  let continuation : Result (SemEnv Value × List Dec) Value → State σ → State σ × Result (List Value) Value :=
    fun result state => match result with
    | .err error => (state, .err error)
    | .val (evalEnv, decs) =>
      if state.clock = 0 then timeoutError state else
      let next := evaluateDecs (decClock state) evalEnv decs
      match next.2 with
      | .val newEnv => match declareEnv next.1.evalState (extendDecEnv newEnv evalEnv) with
        | none => typeError next.1
        | some (value, evalState) =>
          ({ next.1 with evalState := resetEnvGeneration st.evalState evalState }, .val [value])
      | .err (.abort error) => (next.1, .err (.abort error))
      | .err error => ({ next.1 with evalState := resetEnvGeneration st.evalState next.1.evalState }, .err error)
  have hcont : ∀ next result, doEvalRes (β := Value) values st = (next, result) →
      isClockIoMono (continuation result) next := by
    intro next result heval
    cases result with
    | err error => exact isClockIoMono_err (α := List Value) next error
    | val info =>
      rcases info with ⟨evalEnv, decs⟩
      let finish : State σ → State σ × Result (List Value) Value := fun state =>
        let output := evaluateDecs state evalEnv decs
        match output.2 with
        | .val newEnv => match declareEnv output.1.evalState (extendDecEnv newEnv evalEnv) with
          | none => typeError output.1
          | some (value, evalState) =>
            ({ output.1 with evalState := resetEnvGeneration st.evalState evalState }, .val [value])
        | .err (.abort error) => (output.1, .err (.abort error))
        | .err error => ({ output.1 with evalState := resetEnvGeneration st.evalState output.1.evalState }, .err error)
      have checked := clockIo_checked next finish (by
        intro nonzero
        have base := clockIo_finishEval (decClock next) st.evalState evalEnv
          (fun state => evaluateDecs state evalEnv decs) (ih next evalEnv decs heval nonzero)
        have fnEq : (fun state => let (output, result) := evaluateDecs state evalEnv decs; match result with
            | .val newEnv => match declareEnv output.evalState (extendDecEnv newEnv evalEnv) with
              | none => typeError output
              | some (value, evalState) =>
                ({ output with evalState := resetEnvGeneration st.evalState evalState }, .val [value])
            | .err (.abort error) => (output, .err (.abort error))
            | .err (.raise value) => ({ output with evalState := resetEnvGeneration st.evalState output.evalState }, .err (.raise value))) = finish := by
          funext state
          dsimp only [finish]
          cases hevalDecs : evaluateDecs state evalEnv decs with
          | mk output result => cases result with
            | val inner => rfl
            | err error => cases error <;> rfl
        rw [fnEq] at base
        exact base)
      simpa only [continuation, finish, timeoutError] using checked
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    rfl
  have fixed := isClockIoMono_bind (fun state => doEvalRes (β := Value) values state) continuation st
    ⟨clockIo_doEvalRes st values, hcont, htimeout⟩
  have fixedEq : (fun state => let (next, result) := doEvalRes (β := Value) values state; continuation result next) =
      (fun state => choose st.evalState state) := by
    funext state
    dsimp only [choose]
  rw [fixedEq] at fixed
  have independent : ∀ state clock, accessor { state with clock } = accessor state := by
    intro state clock
    rfl
  have result := isClockIoMono_accSafe accessor st none choose ⟨independent, Classical.em _, fixed⟩
  have fnEq : (fun state => choose (accessor state) state) =
      (fun state =>
        let decoded := fixClock state (doEvalRes (β := Value) values state)
        match decoded.2 with
        | .err error => (decoded.1, .err error)
        | .val (evalEnv, decs) =>
          if decoded.1.clock = 0 then timeoutError decoded.1 else
          let next := fixClock (decClock decoded.1) (evaluateDecs (decClock decoded.1) evalEnv decs)
          match next.2 with
          | .val newEnv => match declareEnv next.1.evalState (extendDecEnv newEnv evalEnv) with
            | none => typeError next.1
            | some (value, evalState) =>
              ({ next.1 with evalState := resetEnvGeneration state.evalState evalState }, .val [value])
          | .err (.abort error) => (next.1, .err (.abort error))
          | .err error => ({ next.1 with evalState := resetEnvGeneration state.evalState next.1.evalState }, .err error)) := by
    funext state
    simp only [fixClockDoEvalRes, choose, accessor]
    cases heval : doEvalRes (β := Value) values state with
    | mk decoded outcome =>
      cases outcome with
      | err error => rfl
      | val info =>
        rcases info with ⟨evalEnv, decs⟩
        simp only
        split
        · rfl
        · rw [(fixClockEvaluate (decClock decoded) evalEnv [] decs).2]
  rw [fnEq] at result
  exact result

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem clockIoEvaluate_app {σ : Type} (st : State σ) (env : SemEnv Value)
    (op : AstHOL.Op) (args : List AstHOL.Exp)
    (ihArgs : isClockIoMono (fun state => evaluate state env args.reverse) st)
    (ihFun : ∀ next values callEnv body, evaluate st env args.reverse = (next, .val values) →
      getOpClass op = .funApp → doOpApp values.reverse = some (callEnv, body) → next.clock ≠ 0 →
      isClockIoMono (fun state => evaluate state callEnv [body]) (decClock next))
    (ihForce : ∀ next values thunk callEnv body, evaluate st env args.reverse = (next, .val values) →
      getOpClass op = .force → destThunk values.reverse next.refs = .isThunk .notEvaluated thunk →
      doOpApp [thunk, .conv none []] = some (callEnv, body) → next.clock ≠ 0 →
      isClockIoMono (fun state => evaluate state callEnv [body]) (decClock next))
    (ihEval : ∀ next values decoded evalEnv decs, evaluate st env args.reverse = (next, .val values) →
      getOpClass op = .evalOp → doEvalRes (β := Value) values.reverse next = (decoded, .val (evalEnv, decs)) →
      decoded.clock ≠ 0 → isClockIoMono (fun state => evaluateDecs state evalEnv decs) (decClock decoded)) :
    isClockIoMono (fun state => evaluate state env [.app op args]) st := by
  let continuation : Result (List Value) Value → State σ → State σ × Result (List Value) Value :=
    fun result state => match result with
    | .err error => (state, .err error)
    | .val reversed =>
      let values := reversed.reverse
      match getOpClass op with
      | .funApp => match doOpApp values with
        | none => typeError state
        | some (callEnv, body) => if state.clock = 0 then timeoutError state else evaluate (decClock state) callEnv [body]
      | .force => match destThunk values state.refs with
        | .badRef | .notThunk => typeError state
        | .isThunk .evaluated value => (state, .val [value])
        | .isThunk .notEvaluated thunk => match doOpApp [thunk, .conv none []] with
          | none => typeError state
          | some (callEnv, body) =>
            if state.clock = 0 then timeoutError state else
            let next := evaluate (decClock state) callEnv [body]
            match next.2 with
            | .err error => (next.1, .err error)
            | .val newValues => match updateThunk values next.1.refs newValues with
              | none => typeError next.1
              | some refs => ({ next.1 with refs }, .val newValues)
      | .evalOp =>
        let decoded := fixClock state (doEvalRes (β := Value) values state)
        match decoded.2 with
        | .err error => (decoded.1, .err error)
        | .val (evalEnv, decs) =>
          if decoded.1.clock = 0 then timeoutError decoded.1 else
          let next := fixClock (decClock decoded.1) (evaluateDecs (decClock decoded.1) evalEnv decs)
          match next.2 with
          | .val newEnv => match declareEnv next.1.evalState (extendDecEnv newEnv evalEnv) with
            | none => typeError next.1
            | some (value, evalState) => ({ next.1 with evalState := resetEnvGeneration state.evalState evalState }, .val [value])
          | .err (.abort error) => (next.1, .err (.abort error))
          | .err error => ({ next.1 with evalState := resetEnvGeneration state.evalState next.1.evalState }, .err error)
      | .simple => match doApp (state.refs, state.ffi) op values with
        | none => typeError state
        | some ((refs, ffi), output) => ({ state with refs, ffi }, listResult output)
  have hcont : ∀ next result, evaluate st env args.reverse = (next, result) →
      isClockIoMono (continuation result) next := by
    intro next result heval
    cases result with
    | err error => exact isClockIoMono_err (α := List Value) next error
    | val reversed =>
      cases hc : getOpClass op with
      | funApp =>
        cases happ : doOpApp reversed.reverse with
        | none => simpa only [continuation, hc, happ, typeError] using isClockIoMono_err (α := List Value) next (.abort .typeError)
        | some call =>
          rcases call with ⟨callEnv, body⟩
          have checked := clockIo_checkedCall next callEnv body (ihFun next reversed callEnv body heval hc happ)
          simpa only [continuation, hc, happ] using checked
      | force =>
        have force := clockIo_force next reversed.reverse (by
          intro thunk callEnv body hd happ nonzero
          exact ihForce next reversed thunk callEnv body heval hc hd happ nonzero)
        simpa only [continuation, hc] using force
      | evalOp =>
        have eval := clockIo_evalOperation next reversed.reverse (by
          intro decoded evalEnv decs hevalDecoded nonzero
          exact ihEval next reversed decoded evalEnv decs heval hc hevalDecoded nonzero)
        simpa only [continuation, hc] using eval
      | simple =>
        cases happ : doApp (next.refs, next.ffi) op reversed.reverse with
        | none => simp [isClockIoMono, continuation, hc, happ, typeError, ioEventsMonoHOL]
        | some output =>
          rcases output with ⟨⟨refs, ffi⟩, result⟩
          have length := doApp_refs_length (next.refs, next.ffi) op reversed.reverse ((refs, ffi), result) happ
          have trace := doApp_ioEventsMono next.refs refs next.ffi ffi op reversed.reverse result happ
          simp [isClockIoMono, continuation, hc, happ, length, ioEventsMonoHOL]
          constructor
          · exact trace
          · intros
            assumption
  have htimeout : ∀ next, continuation (.err (.abort .timeoutError)) next =
      (next, .err (.abort .timeoutError)) := by
    intro next
    rfl
  have bound := isClockIoMono_bind (fun state => evaluate state env args.reverse) continuation st
    ⟨ihArgs, hcont, htimeout⟩
  have fnEq : (fun state => let (next, result) := evaluate state env args.reverse; continuation result next) =
      (fun state => evaluate state env [.app op args]) := by
    funext state
    simp only [evaluate]
    rw [(fixClockEvaluate state env args.reverse []).1]
    cases heval : evaluate state env args.reverse with
    | mk next result =>
      cases result with
      | err error => rfl
      | val values =>
        dsimp only [continuation]
        cases getOpClass op <;> rfl
  rw [fnEq] at bound
  exact bound

end Flapjack.EvaluateProps
