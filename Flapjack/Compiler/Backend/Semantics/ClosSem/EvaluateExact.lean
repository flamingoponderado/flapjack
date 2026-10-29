import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel

/-! Clocked closure evaluation without an external recursion bound. This
proof-side evaluator remains untagged pending source and carrier review. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

private noncomputable def headValue (values : List Value) : Value :=
  @Flapjack.holHd Value ⟨unitValue⟩ values

private noncomputable def lastValue (values : List Value) : Value :=
  @Flapjack.holLast Value ⟨unitValue⟩ values

private def typeError {C F : Type} (state : State C F) : EvalResult C F :=
  (.err (.abort .typeError), state)

private def timeoutError {C F : Type} (state : State C F) : EvalResult C F :=
  (.err (.abort .timeoutError), state)

@[simp] private theorem headValue_cons (value : Value) (tail : List Value) :
    headValue (value :: tail) = value := rfl

@[simp] private theorem typeError_eq {C F : Type} (state : State C F) :
    typeError state = (.err (.abort .typeError), state) := rfl

@[simp] private theorem timeoutError_eq {C F : Type} (state : State C F) :
    timeoutError state = (.err (.abort .timeoutError), state) := rfl

mutual
/-- Evaluate closure expressions using the HOL clock. -/
noncomputable def evaluate {C F : Type} (expressions : List ClosLang.Exp)
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
    | .var _ index => match env[index]? with
      | none => typeError state
      | some value => (.val [value], state)
    | .ifThenElse _ condition yes no =>
      let next := fixClock state (evaluate [condition] env state)
      match next.1 with
      | .err error => (.err error, next.2)
      | .val values => match asBool (headValue values) with
        | none => typeError next.2
        | some true => evaluate [yes] env next.2
        | some false => evaluate [no] env next.2
    | .let _ bindings body =>
      let next := fixClock state (evaluate bindings env state)
      match next.1 with
      | .err error => (.err error, next.2)
      | .val values => evaluate [body] (values ++ env) next.2
    | .raise _ body =>
      let (result, next) := evaluate [body] env state
      match result with
      | .err error => (.err error, next)
      | .val values => (.err (.raise (headValue values)), next)
    | .handle _ body handler =>
      let next := fixClock state (evaluate [body] env state)
      match next.1 with
      | .err (.raise value) => evaluate [handler] (value :: env) next.2
      | other => (other, next.2)
    | .op _ op args =>
      let next := fixClock state (evaluate args env state)
      match next.1 with
      | .err error => (.err error, next.2)
      | .val values => match op with
        | .install => match _installRun : doInstall values.reverse next.2 with
          | (.err error, last) => (.err error, last)
          | (.val installed, last) =>
            let (result, final) := evaluate installed [] last
            match result with
            | .err error => (.err error, final)
            | .val values => (.val [lastValue values], final)
        | .thunkOp .forceThunk => match destThunk values next.2.refs with
          | .badRef | .notThunk => typeError next.2
          | .isThunk .evaluated value => (.val [value], next.2)
          | .isThunk .notEvaluated value =>
            let (result, last) := evaluate [appUnit (.var .none 0)] [value] next.2
            match result with
            | .err error => (.err error, last)
            | .val forced => match updateThunk values last.refs forced with
              | none => typeError last
              | some refs => (.val forced, { last with refs := refs })
        | _ => match doApp op values.reverse next.2 with
          | .err error => (.err error, next.2)
          | .val (value, last) => (.val [value], last)
    | .fn _ location selected arity body =>
      if arity ≤ state.maxApp ∧ arity ≠ 0 then
        let captured := match selected with | none => some env | some names => lookupVars names env
        match captured with
        | none => typeError state
        | some values => (.val [.closure location [] values arity body], state)
      else typeError state
    | .letrec _ location selected functions body =>
      if functions.all (fun (arity, _) => arity ≤ state.maxApp && arity != 0) then
        let captured := match selected with | none => some env | some names => lookupVars names env
        match captured with
        | none => typeError state
        | some values =>
          let recursive := (List.range functions.length).map (fun i => Value.recclosure location [] values functions i)
          evaluate [body] (recursive ++ env) state
      else typeError state
    | .app _ location function args =>
      if args.isEmpty then typeError state else
        let next := fixClock state (evaluate args env state)
        match next.1 with
        | .err error => (.err error, next.2)
        | .val values =>
          let last := fixClock next.2 (evaluate [function] env next.2)
          match last.1 with
          | .err error => (.err error, last.2)
          | .val functionValues => evaluateApp location (headValue functionValues) values last.2
    | .tick _ body =>
      if state.clock = 0 then timeoutError state
      else evaluate [body] env (decClock 1 state)
    | .call _ ticks location args =>
      let next := fixClock state (evaluate args env state)
      match next.1 with
      | .err error => (.err error, next.2)
      | .val values => match findCode location values next.2.code with
        | none => typeError next.2
        | some (values, body) =>
          if next.2.clock < ticks + 1 then timeoutError { next.2 with clock := 0 }
          else evaluate [body] values (decClock (ticks + 1) next.2)
termination_by (state.clock, expsWeight expressions, 0)
decreasing_by
  all_goals try simp only [Prod.lex_def, expsWeight, expWeight, fixClock, decClock]
  all_goals try (have := expWeight_pos second)
  all_goals try (have := doInstall_success_clock _ _ _ _ (by assumption))
  all_goals try
    have clockBound : next.2.clock ≤ state.clock := by
      dsimp only [next, fixClock]
      exact Nat.min_le_left _ _
  all_goals try dsimp only [next, last] at *
  all_goals try simp_all [fixClock, expsWeight, expWeight, appUnit]
  all_goals try exact opWeight_gt _ op args
  all_goals try omega

/-- Apply a closure, consuming its argument list and clock. -/
noncomputable def evaluateApp {C F : Type} (location : Option Nat) (function : Value)
    (args : List Value) (state : State C F) : EvalResult C F :=
  match args with
  | [] => (.val [function], state)
  | _ :: _ => match _closureRun : destClosure state.maxApp location function args with
    | none => typeError state
    | some (.partialApp value) =>
      if state.clock < args.length then timeoutError { state with clock := 0 }
      else (.val [value], decClock args.length state)
    | some (.fullApp body env rest) =>
      let cost := args.length - rest.length
      if state.clock < cost then timeoutError { state with clock := 0 } else
        let start := decClock cost state
        let next := fixClock start (evaluate [body] env start)
        match next.1 with
        | .val [value] => evaluateApp location value rest next.2
        | other => (other, next.2)
termination_by (state.clock, 0, args.length)
decreasing_by
  all_goals simp_wf
  all_goals try (have := destClosure_full_remaining_lt _ _ _ _ _ _ _ (by assumption))
  all_goals try dsimp only [next, start, cost] at *
  all_goals try simp_all [Prod.lex_def, fixClock, decClock]
  all_goals try omega
end

end Flapjack.Compiler.Backend.ClosSem
