import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply
import Flapjack.Compiler.Backend.Semantics.FlatSem.Eval
import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch

/-! A fuel-bounded version of the original flat evaluator. Fuel exhaustion is
represented separately from the original clock timeout. The unbounded HOL
evaluator and the proof that sufficient fuel exists remain open. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Basis.Pure.MlString

abbrev EvalResult (C F : Type) := State C F × Result (List Value) Value

private def typeError {C F : Type} (state : State C F) : EvalResult C F :=
  (state, .err (.abort .typeError))

private def timeoutError {C F : Type} (state : State C F) : EvalResult C F :=
  (state, .err (.abort .timeoutError))

/-- Select a row and reject duplicate pattern bindings. -/
def selectRow {C F : Type} (state : State C F) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (value noMatch : Value) : Except (ErrorResult Value) (List (VarN × Value) × FlatLang.Exp) :=
  match pmatchRows rows state value with
  | .typeError => .error (.abort .typeError)
  | .noMatch => .error (.raise noMatch)
  | .match (bindings, pattern, expression) =>
    if (FlatLang.patBindings pattern).Nodup then .ok (bindings, expression)
    else .error (.abort .typeError)

mutual
/-- Evaluate flat expressions with an explicit recursion bound. `none` means
the bound ran out; clock timeout and other semantic errors remain in `some`.
The source uses `HD` on singleton results; an impossible empty successful
result is treated as a type error until singleton preservation is proved. -/
noncomputable def evaluateFuel {C F : Type} : Nat → Environment Value → State C F →
    List FlatLang.Exp → Option (EvalResult C F)
  | 0, _, _, _ => none
  | fuel + 1, env, state, expressions => do
    match expressions with
    | [] => some (state, .val [])
    | first :: second :: rest =>
      let firstResult ← evaluateFuel fuel env state [first]
      let (next, result) := fixClock state firstResult
      match result with
      | .err error => some (next, .err error)
      | .val [] => some (typeError next)
      | .val (value :: _) =>
        let (last, result) ← evaluateFuel fuel env next (second :: rest)
        match result with
        | .err error => some (last, .err error)
        | .val values => some (last, .val (value :: values))
    | [expression] => match expression with
      | .lit _ lit => some (state, .val [.litv lit])
      | .varLocal _ name => match env.v.lookup name with
        | some value => some (state, .val [value])
        | none => some (typeError state)
      | .fn _ name body => some (state, .val [.closure env name body])
      | .raise _ body =>
        let (next, result) ← evaluateFuel fuel env state [body]
        match result with
        | .err error => some (next, .err error)
        | .val (value :: _) => some (next, .err (.raise value))
        | .val [] => some (typeError next)
      | .handle _ body rows =>
        let inner ← evaluateFuel fuel env state [body]
        let (next, result) := fixClock state inner
        match result with
        | .err (.raise value) => match selectRow next rows value value with
          | .error error => some (next, .err error)
          | .ok (bindings, body) => evaluateFuel fuel { env with v := bindings ++ env.v } next [body]
        | result => some (next, result)
      | .con _ constructor args =>
        let (next, result) ← evaluateFuel fuel env state args.reverse
        match result with
        | .err error => some (next, .err error)
        | .val values => some (next, .val [.conv constructor values.reverse])
      | .app _ op args =>
        let inner ← evaluateFuel fuel env state args.reverse
        let (next, result) := fixClock state inner
        match result with
        | .err error => some (next, .err error)
        | .val values =>
          match op with
          | .src .opapp => match doOpApp values.reverse with
            | none => some (typeError next)
            | some (newEnv, body) =>
              if next.clock = 0 then some (timeoutError next)
              else evaluateFuel fuel newEnv (decClock next) [body]
          | .src .eval => match doEval values.reverse next.evalConfig with
            | none => some (typeError next)
            | some (decs, config, result) =>
              let next := { next with evalConfig := config }
              if next.clock = 0 then some (timeoutError next) else do
                let (last, error) ← evaluateDecsFuel fuel (decClock next) decs
                match error with
                | none => some (last, .val [result])
                | some error => some (last, .err error)
          | .src (.thunkOp .forceThunk) => match destThunk values next.refs with
            | .badRef | .notThunk => some (typeError next)
            | .isThunk .evaluated value => some (next, .val [value])
            | .isThunk .notEvaluated value =>
              let name := ofString "f"
              let app : FlatLang.Exp := .app .none (.src .opapp)
                [.varLocal .none name, .con .none none []]
              let (last, result) ← evaluateFuel fuel ⟨[(name, value)]⟩ next [app]
              match result with
              | .err error => some (last, .err error)
              | .val values' => match updateThunk values last.refs values' with
                | none => some (typeError last)
                | some refs => some ({ last with refs := refs }, .val values')
          | _ => match doApp next op values.reverse with
            | none => some (typeError next)
            | some (last, .err error) => some (last, .err error)
            | some (last, .val value) => some (last, .val [value])
      | .if_ _ cond yes no =>
        let inner ← evaluateFuel fuel env state [cond]
        let (next, result) := fixClock state inner
        match result with
        | .err error => some (next, .err error)
        | .val [] => some (typeError next)
        | .val (value :: _) => match doIf value yes no with
          | none => some (typeError next)
          | some body => evaluateFuel fuel env next [body]
      | .mat _ body rows =>
        let inner ← evaluateFuel fuel env state [body]
        let (next, result) := fixClock state inner
        match result with
        | .err error => some (next, .err error)
        | .val [] => some (typeError next)
        | .val (value :: _) => match selectRow next rows value bindExnV with
          | .error error => some (next, .err error)
          | .ok (bindings, body) => evaluateFuel fuel { env with v := bindings ++ env.v } next [body]
      | .let_ _ name first body =>
        let inner ← evaluateFuel fuel env state [first]
        let (next, result) := fixClock state inner
        match result with
        | .err error => some (next, .err error)
        | .val [] => some (typeError next)
        | .val (value :: _) =>
          let bindings := match name with | none => env.v | some name => (name, value) :: env.v
          evaluateFuel fuel { env with v := bindings } next [body]
      | .letrec _ funs body =>
        if (funs.map Prod.fst).Nodup then
          evaluateFuel fuel { env with v := buildRecEnv funs env env.v } state [body]
        else some (typeError state)

/-- Evaluate top-level declarations with the same separate recursion bound. -/
noncomputable def evaluateDecsFuel {C F : Type} : Nat → State C F → List FlatLang.Exp →
    Option (State C F × Option (ErrorResult Value))
  | 0, _, _ => none
  | _ + 1, state, [] => some (state, none)
  | fuel + 1, state, declaration :: rest => do
    let result ← evaluateFuel fuel ⟨[]⟩ state [declaration]
    let (next, result) := fixClock state result
    match result with
    | .err error => some (next, some error)
    | .val [.conv none []] => evaluateDecsFuel fuel next rest
    | .val _ => some (next, some (.abort .typeError))
end

end Flapjack.Compiler.Backend.FlatSem
