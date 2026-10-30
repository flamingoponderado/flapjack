import Flapjack.Compiler.Backend.Semantics.BvlSem.Measure
import Flapjack.Misc.ListEl

/-! Clocked BVL evaluation, retaining the original clock clamps. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL

/-- The result and state pair returned by BVL evaluation. -/
abbrev EvalResult (C F : Type) := Result (List Value) Value × State C F

private noncomputable def headValue (values : List Value) : Value :=
  @Flapjack.holHd Value ⟨unitValue⟩ values

private def typeError {C F : Type} (state : State C F) : EvalResult C F :=
  (.err (.abort .typeError), state)

private def timeoutError {C F : Type} (state : State C F) : EvalResult C F :=
  (.err (.abort .timeoutError), state)

@[simp] private theorem headValue_cons (value : Value) (tail : List Value) :
    headValue (value :: tail) = value := rfl

@[simp] private theorem timeoutError_eq {C F : Type} (state : State C F) :
    timeoutError state = (.err (.abort .timeoutError), state) := rfl

/-- Clocked, source-shaped BVL evaluation. This proof-side infrastructure is
untagged until the dispatcher, the use of `holHd` on singleton evaluations,
and the original clock-clamp elimination have been reviewed against HOL. -/
noncomputable def evaluate {C F : Type} (expressions : List Bvl.Exp)
    (env : List Value) (state : State C F) : EvalResult C F :=
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
      | .val values => (.err (.raise (headValue values)), next)
    | .handle body handler =>
      let next := fixClock state (evaluate [body] env state)
      match next.1 with
      | .err (.raise value) => evaluate [handler] (value :: env) next.2
      | other => (other, next.2)
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
            else evaluate [body] args (decClock 1 state)
    | .call ticks dest args =>
      let next := fixClock state (evaluate args env state)
      match next.1 with
      | .err error => (.err error, next.2)
      | .val values => match findCode dest values next.2.code with
        | none => typeError next.2
        | some (values, body) =>
          if next.2.clock < ticks + 1 then timeoutError { next.2 with clock := 0 }
          else evaluate [body] values (decClock (ticks + 1) next.2)
termination_by (state.clock, expsWeight expressions)
decreasing_by
  all_goals try simp only [Prod.lex_def, expsWeight, expWeight, fixClock, decClock]
  all_goals try (have := expWeight_pos second)
  all_goals try
    have clockBound : next.2.clock ≤ state.clock := by
      dsimp only [next, fixClock]
      exact Nat.min_le_left _ _
  all_goals try dsimp only [next] at *
  all_goals try simp_all [fixClock]
  all_goals try omega

end Flapjack.Compiler.Backend.BvlSem
