import Flapjack.Compiler.Backend.Semantics.ClosSem.Measure

/-! Bounded approximation of closure evaluation. Exhausting the bound is
separate from the original clock timeout. The unbounded HOL evaluator and its
correspondence theorem remain open. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- Evaluation result in the same order as the HOL closure semantics. -/
abbrev EvalResult (C F : Type) := Result (List Value) Value × State C F

/-- Clamp the result clock to its input clock. -/
def fixClock {C F : Type} (state : State C F) (result : EvalResult C F) : EvalResult C F :=
  (result.1, { result.2 with clock := min state.clock result.2.clock })

private noncomputable def headValue (values : List Value) : Value :=
  @Flapjack.holHd Value ⟨unitValue⟩ values

private noncomputable def lastValue (values : List Value) : Value :=
  @Flapjack.holLast Value ⟨unitValue⟩ values

private def typeError {C F : Type} (state : State C F) : EvalResult C F :=
  (.err (.abort .typeError), state)

private def timeoutError {C F : Type} (state : State C F) : EvalResult C F :=
  (.err (.abort .timeoutError), state)

mutual
/-- Closure evaluation with an extra recursion bound. `none` signals that
the bound was exhausted; it is not an original evaluation outcome. -/
noncomputable def evaluateFuel {C F : Type} : Nat → List ClosLang.Exp → List Value → State C F → Option (EvalResult C F)
  | 0, _, _, _ => none
  | fuel + 1, expressions, env, state => do
    match expressions with
    | [] => some (.val [], state)
    | first :: second :: rest =>
      let firstResult ← evaluateFuel fuel [first] env state
      let (result, next) := fixClock state firstResult
      match result with
      | .err error => some (.err error, next)
      | .val values =>
        let (result, last) ← evaluateFuel fuel (second :: rest) env next
        match result with
        | .err error => some (.err error, last)
        | .val tail => some (.val (headValue values :: tail), last)
    | [expression] => match expression with
      | .var _ index => match env[index]? with
        | none => some (typeError state)
        | some value => some (.val [value], state)
      | .ifThenElse _ condition yes no =>
        let conditionResult ← evaluateFuel fuel [condition] env state
        let (result, next) := fixClock state conditionResult
        match result with
        | .err error => some (.err error, next)
        | .val values => match asBool (headValue values) with
          | none => some (typeError next)
          | some true => evaluateFuel fuel [yes] env next
          | some false => evaluateFuel fuel [no] env next
      | .let _ bindings body =>
        let bindingResult ← evaluateFuel fuel bindings env state
        let (result, next) := fixClock state bindingResult
        match result with
        | .err error => some (.err error, next)
        | .val values => evaluateFuel fuel [body] (values ++ env) next
      | .raise _ body =>
        let (result, next) ← evaluateFuel fuel [body] env state
        match result with
        | .err error => some (.err error, next)
        | .val values => some (.err (.raise (headValue values)), next)
      | .handle _ body handler =>
        let bodyResult ← evaluateFuel fuel [body] env state
        let (result, next) := fixClock state bodyResult
        match result with
        | .err (.raise value) => evaluateFuel fuel [handler] (value :: env) next
        | other => some (other, next)
      | .op _ op args =>
        let argsResult ← evaluateFuel fuel args env state
        let (result, next) := fixClock state argsResult
        match result with
        | .err error => some (.err error, next)
        | .val values => match op with
          | .install => match doInstall values.reverse next with
            | (.err error, last) => some (.err error, last)
            | (.val installed, last) =>
              let (result, final) ← evaluateFuel fuel installed [] last
              match result with
              | .err error => some (.err error, final)
              | .val values => some (.val [lastValue values], final)
          | .thunkOp .forceThunk => match destThunk values next.refs with
            | .badRef | .notThunk => some (typeError next)
            | .isThunk .evaluated value => some (.val [value], next)
            | .isThunk .notEvaluated value =>
              let (result, last) ← evaluateFuel fuel [appUnit (.var .none 0)] [value] next
              match result with
              | .err error => some (.err error, last)
              | .val forced => match updateThunk values last.refs forced with
                | none => some (typeError last)
                | some refs => some (.val forced, { last with refs := refs })
          | _ => match doApp op values.reverse next with
            | .err error => some (.err error, next)
            | .val (value, last) => some (.val [value], last)
      | .fn _ location selected arity body =>
        if arity ≤ state.maxApp ∧ arity ≠ 0 then
          let captured := match selected with | none => some env | some names => lookupVars names env
          match captured with
          | none => some (typeError state)
          | some values => some (.val [.closure location [] values arity body], state)
        else some (typeError state)
      | .letrec _ location selected functions body =>
        if functions.all (fun (arity, _) => arity ≤ state.maxApp && arity != 0) then
          let captured := match selected with | none => some env | some names => lookupVars names env
          match captured with
          | none => some (typeError state)
          | some values =>
            let recursive := (List.range functions.length).map (fun i => Value.recclosure location [] values functions i)
            evaluateFuel fuel [body] (recursive ++ env) state
        else some (typeError state)
      | .app _ location function args =>
        if args.isEmpty then some (typeError state) else do
          let argsResult ← evaluateFuel fuel args env state
          let (result, next) := fixClock state argsResult
          match result with
          | .err error => some (.err error, next)
          | .val values =>
            let functionResult ← evaluateFuel fuel [function] env next
            let (result, last) := fixClock next functionResult
            match result with
            | .err error => some (.err error, last)
            | .val functionValues => evaluateAppFuel fuel location (headValue functionValues) values last
      | .tick _ body =>
        if state.clock = 0 then some (timeoutError state)
        else evaluateFuel fuel [body] env (decClock 1 state)
      | .call _ ticks location args =>
        let argsResult ← evaluateFuel fuel args env state
        let (result, next) := fixClock state argsResult
        match result with
        | .err error => some (.err error, next)
        | .val values => match findCode location values next.code with
          | none => some (typeError next)
          | some (values, body) =>
            if next.clock < ticks + 1 then some (timeoutError { next with clock := 0 })
            else evaluateFuel fuel [body] values (decClock (ticks + 1) next)

/-- Apply a closure with an extra recursion bound. -/
noncomputable def evaluateAppFuel {C F : Type} : Nat → Option Nat → Value → List Value → State C F → Option (EvalResult C F)
  | 0, _, _, _, _ => none
  | fuel + 1, location, function, args, state =>
    match args with
    | [] => some (.val [function], state)
    | _ :: _ => match destClosure state.maxApp location function args with
      | none => some (typeError state)
      | some (.partialApp value) =>
        if state.clock < args.length then some (timeoutError { state with clock := 0 })
        else some (.val [value], decClock args.length state)
      | some (.fullApp body env rest) =>
        let cost := args.length - rest.length
        if state.clock < cost then some (timeoutError { state with clock := 0 }) else do
          let start := decClock cost state
          let bodyResult ← evaluateFuel fuel [body] env start
          let (result, next) := fixClock start bodyResult
          match result with
          | .val [value] => evaluateAppFuel fuel location value rest next
          | other => some (other, next)
end

end Flapjack.Compiler.Backend.ClosSem
