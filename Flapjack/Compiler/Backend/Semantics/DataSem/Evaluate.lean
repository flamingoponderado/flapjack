module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Apply

@[expose] public section

/-! Clocked execution of data-language programs. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- A stopped program returns either values or an error; `none` continues. -/
abbrev EvalResult (C F : Type) := Option (Result (List Value) Value) × State C F

/-- The original data evaluator's type-error outcome. -/
def typeError {C F : Type} (state : State C F) : EvalResult C F :=
  (some (.err (.abort .typeError)), state)

/-- The original data evaluator's clock-timeout outcome. -/
def timeoutError {C F : Type} (state : State C F) : EvalResult C F :=
  (some (.err (.abort .timeoutError)), state)

@[simp] theorem typeError_eq {C F : Type} (state : State C F) :
    typeError state = (some (.err (.abort .typeError)), state) := rfl

@[simp] theorem timeoutError_eq {C F : Type} (state : State C F) :
    timeoutError state = (some (.err (.abort .timeoutError)), state) := rfl

/-- Clocked execution, retaining the source's timeout, stack, handler, and
clock-clamping behavior. The lexicographic measure is clock then program size. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "evaluate_def" 1349]
noncomputable def evaluate {C F : Type} (program : DataLang.Prog) (state : State C F) : EvalResult C F :=
  match program with
  | .skip => (none, state)
  | .move dest src => match getVar src state.locals with
    | none => typeError state
    | some value => (none, setVar dest value state)
  | .assign dest op names live =>
    if DataLang.opRequiresNames op == live.isNone then typeError state else
      match getVars names state.locals with
      | none => typeError state
      | some values => match cutStateOpt live state with
        | none => typeError state
        | some next => match doApp op values next with
          | .err error => (some (.err error), flushState true (installSfs op next))
          | .val (value, last) => (none, setVar dest value (installSfs op last))
  | .tick =>
    if state.clock = 0 then timeoutError (flushState true state) else (none, decClock state)
  | .makeSpace amount names => match cutEnv names state.locals with
    | none => typeError state
    | some env => (none, addSpace { state with locals := env } amount)
  | .raise name => match getVar name state.locals with
    | none => typeError state
    | some value => match jumpExc state with
      | none => typeError state
      | some next => (some (.err (.raise value)), next)
  | .return names => match getVars names state.locals with
    | none => typeError state
    | some values => (some (.val values), flushState false state)
  | .seq first second =>
    let next := fixClock state (evaluate first state)
    match next.1 with
    | none => evaluate second next.2
    | some result => (some result, next.2)
  | .ifThenElse name yes no => match getVar name state.locals with
    | none => typeError state
    | some value =>
      if isBool true value then evaluate yes state else
      if isBool false value then evaluate no state else typeError state
  | .force ret label src => match getVar src state.locals with
    | none => typeError state
    | some thunk => match destThunk thunk state.refs with
      | .badRef | .notThunk => typeError state
      | .isThunk .evaluated value => match ret with
        | none => (some (.val [value]), flushState false state)
        | some (dest, names) => match cutEnv names state.locals with
          | none => typeError state
          | some env => (none, setVar dest value { state with locals := env })
      | .isThunk .notEvaluated function =>
        match findCode (some label) [thunk, function] state.code state.stackFrameSizes with
        | none => typeError state
        | some (args, body, size) => match ret with
          | none =>
            if state.clock = 0 then timeoutError { state with stack := [], locals := .ln } else
              let result := evaluate body (callEnv args size (decClock state))
              match result.1 with
              | none => typeError result.2
              | some value => (some value, result.2)
          | some (dest, names) => match cutEnv names state.locals with
            | none => typeError state
            | some env =>
              let callState := callEnv args size (pushEnv env false (decClock state))
              if state.clock = 0 then timeoutError { callState with stack := [], locals := .ln } else
                let result := fixClock callState (evaluate body callState)
                match result.1 with
                | some (.val [value]) => match popEnv result.2 with
                  | none => typeError result.2
                  | some next => (none, setVar dest value next)
                | some (.val _) | none => typeError result.2
                | some (.err error) => (some (.err error), result.2)
  | .call ret dest names handler => match getVars names state.locals with
    | none => typeError state
    | some values => match findCode dest values state.code state.stackFrameSizes with
      | none => typeError state
      | some (args, body, size) => match ret with
        | none =>
          if handler.isSome then typeError state else
          if state.clock = 0 then timeoutError (flushState true state) else
            let result := evaluate body (callEnv args size (decClock state))
            match result.1 with
            | none => typeError result.2
            | some value => (some value, result.2)
        | some (returns, live) =>
          if !returns.Nodup then typeError state else
          match cutEnv live state.locals with
          | none => typeError state
          | some env =>
            let callState := callEnv args size (pushEnv env handler.isSome (decClock state))
            if state.clock = 0 then timeoutError { callState with stack := [], locals := .ln } else
              let result := fixClock callState (evaluate body callState)
              match result.1 with
              | some (.val values) =>
                if values.length = returns.length then match popEnv result.2 with
                  | none => typeError result.2
                  | some next => (none, setVars returns values next)
                else typeError result.2
              | some (.err (.raise value)) => match handler with
                | none => (some (.err (.raise value)), result.2)
                | some (name, body) => evaluate body (setVar name value result.2)
              | none => typeError result.2
              | some (.err error) => (some (.err error), result.2)
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals simp_wf
  all_goals try (simp_all [fixClock, decClock, callEnv, pushEnv, setVar])
  all_goals omega

end Flapjack.Compiler.Backend.DataSem
