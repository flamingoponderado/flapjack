import Flapjack.Compiler.Backend.Semantics.BviSem.Measure
import Flapjack.Misc.ListEl

/-! Clocked BVI evaluation with the source's explicit clock clamps. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value unitValue boolValue asBool findCode)
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Result and state returned by BVI evaluation. -/
abbrev EvalResult (C F : Type) := BviResult × BviState C F

private noncomputable def headValue (values : List Value) : Value :=
  @Flapjack.holHd Value ⟨unitValue⟩ values

private def typeError {C F : Type} (state : BviState C F) : EvalResult C F :=
  (.err (.abort .typeError), state)

private def timeoutError {C F : Type} (state : BviState C F) : EvalResult C F :=
  (.err (.abort .timeoutError), state)

@[simp] private theorem typeError_eq {C F : Type} (state : BviState C F) :
    typeError state = (.err (.abort .typeError), state) := rfl

@[simp] private theorem timeoutError_eq {C F : Type} (state : BviState C F) :
    timeoutError state = (.err (.abort .timeoutError), state) := rfl

/-- Clocked, source-shaped BVI evaluation. This remains untagged while the
primitive dispatcher and arbitrary-state bridge await source qualification,
and until the evaluator's termination and clock clauses are reviewed against
the original induction theorem. -/
noncomputable def evaluate {C F : Type} (expressions : List Bvi.Exp)
    (env : List Value) (state : BviState C F) : EvalResult C F :=
  match expressions with
  | [] => (.val [], state)
  | first :: second :: rest =>
    let next := fixClock state (evaluate [first] env state)
    match next.1 with
    | .err error => (.err error, next.2)
    | .val values =>
      let (result, last) := evaluate (second :: rest) env next.2
      match result with
      | .err error => (.err error, last)
      | .val tail => (.val (headValue values :: tail), last)
  | [expression] => match expression with
    | .var index => match env[index]? with
      | none => typeError state
      | some value => (.val [value], state)
    | .ifThenElse condition yes no =>
      let next := fixClock state (evaluate [condition] env state)
      match next.1 with
      | .err error => (.err error, next.2)
      | .val values => match asBool (headValue values) with
        | none => typeError next.2
        | some true => evaluate [yes] env next.2
        | some false => evaluate [no] env next.2
    | .let bindings body =>
      let next := fixClock state (evaluate bindings env state)
      match next.1 with
      | .err error => (.err error, next.2)
      | .val values => evaluate [body] (values ++ env) next.2
    | .raise body =>
      let (result, next) := evaluate [body] env state
      match result with
      | .err error => (.err error, next)
      | .val values => (.err (.raise (.exn (headValue values))), next)
    | .return args =>
      let (result, next) := evaluate args env state
      match result with
      | .err error => (.err error, next)
      | .val values => (.err (.raise (.ret values)), next)
    | .op op args =>
      let next := fixClock state (evaluate args env state)
      match next.1 with
      | .err error => (.err error, next.2)
      | .val values => match doApp op values.reverse next.2 with
        | .err error => (.err error, next.2)
        | .val (value, last) => (.val [value], last)
    | .tick body =>
      if state.clock = 0 then timeoutError state
      else evaluate [body] env (decClock 1 state)
    | .force location index =>
      match env[index]? with
      | none => typeError state
      | some thunk => match destThunk thunk state.refs with
        | .badRef | .notThunk => typeError state
        | .isThunk .evaluated value => (.val [value], state)
        | .isThunk .notEvaluated function =>
          match findCode (some location) [thunk, function] state.code with
          | none => typeError state
          | some (args, body) =>
            if state.clock = 0 then timeoutError { state with clock := 0 }
            else match evaluate [body] args (decClock 1 state) with
              | (.err (.raise (.ret _)), next) => typeError next
              | other => other
    | .call ticks dest args handler =>
      if dest.isNone && handler.isSome then typeError state else
      let next := fixClock state (evaluate args env state)
      match next.1 with
      | .err error => (.err error, next.2)
      | .val values => match findCode dest values next.2.code with
        | none => typeError next.2
        | some (values, body) =>
          if next.2.clock < ticks + 1 then timeoutError { next.2 with clock := 0 }
          else
            let callState := decClock (ticks + 1) next.2
            let called := fixClock callState (evaluate [body] values callState)
            match called.1 with
            | .err (.raise (.exn value)) => match handler with
              | none => (.err (.raise (.exn value)), called.2)
              | some handler => match evaluate [handler] (value :: env) called.2 with
                | (.err (.raise (.ret _)), last) => typeError last
                | other => other
            | .err (.raise (.ret _)) => typeError called.2
            | other => (other, called.2)
    | .letCall rets ticks dest args body =>
      let next := fixClock state (evaluate args env state)
      match next.1 with
      | .err error => (.err error, next.2)
      | .val values => match findCode (some dest) values next.2.code with
        | none => typeError next.2
        | some (values, callee) =>
          if next.2.clock < ticks + 1 then timeoutError { next.2 with clock := 0 }
          else
            let callState := decClock (ticks + 1) next.2
            let called := fixClock callState (evaluate [callee] values callState)
            match called.1 with
            | .val _ => typeError called.2
            | .err (.raise (.ret values)) =>
              if values.length = rets then evaluate [body] (values ++ env) called.2
              else typeError called.2
            | other => (other, called.2)
termination_by (state.clock, expsWeight expressions)
decreasing_by
  all_goals try simp only [Prod.lex_def, expsWeight, expWeight, fixClock, decClock]
  all_goals try (have := expWeight_pos second)
  all_goals try
    have clockBound : next.2.clock ≤ state.clock := by
      dsimp only [next, fixClock]
      exact Nat.min_le_left _ _
  all_goals try dsimp only [next, called, callState] at *
  all_goals try simp_all [fixClock]
  all_goals try omega
  all_goals cases handler <;> simp [expWeight] <;> omega

end Flapjack.Compiler.Backend.BviSem
