import Flapjack.Compiler.Backend.Semantics.FlatSem.Measure
import Flapjack.Misc.ListEl

/-! Clocked flat evaluation without an extra fuel parameter. The definition is
untagged pending complete review against HOL and the source numeric carrier.
Lean currently fails to derive the generated functional induction principle for
this mutual well-founded definition; proofs need an explicit induction over
the clock and expression-weight measure until that issue is resolved. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Basis.Pure.MlString

private noncomputable def headValue (values : List Value) : Value :=
  @Flapjack.holHd Value ⟨unitValue⟩ values

private def typeError {C F : Type} (state : State C F) : EvalResult C F :=
  (state, .err (.abort .typeError))

private def timeoutError {C F : Type} (state : State C F) : EvalResult C F :=
  (state, .err (.abort .timeoutError))

@[simp] private theorem headValue_cons (value : Value) (tail : List Value) :
    headValue (value :: tail) = value := rfl

@[simp] private theorem typeError_eq {C F : Type} (state : State C F) :
    typeError state = (state, .err (.abort .typeError)) := rfl

@[simp] private theorem timeoutError_eq {C F : Type} (state : State C F) :
    timeoutError state = (state, .err (.abort .timeoutError)) := rfl

/-- Lift a primitive operation's result into the evaluator's singleton-result
form, including the original type-error behavior. -/
noncomputable def applyResult {C F : Type} (state : State C F) (op : FlatLang.Op)
    (values : List Value) : EvalResult C F :=
  match doApp state op values with
  | none => typeError state
  | some (next, .err error) => (next, .err error)
  | some (next, .val value) => (next, .val [value])

mutual
/-- Evaluate flat expressions using the original clock, without fuel. -/
noncomputable def evaluate {C F : Type} (env : Environment Value) (state : State C F)
    (expressions : List FlatLang.Exp) : EvalResult C F :=
  match expressions with
  | [] => (state, .val [])
  | first :: second :: rest =>
    let firstResult := fixClock state (evaluate env state [first])
    match firstResult.2 with
    | .err error => (firstResult.1, .err error)
    | .val values =>
      let last := evaluate env firstResult.1 (second :: rest)
      match last.2 with
      | .err error => (last.1, .err error)
      | .val tail => (last.1, .val (headValue values :: tail))
  | [expression] => match expression with
    | .lit _ lit => (state, .val [.litv lit])
    | .varLocal _ name => match env.v.lookup name with
      | some value => (state, .val [value])
      | none => typeError state
    | .fn _ name body => (state, .val [.closure env name body])
    | .raise _ body =>
      let next := evaluate env state [body]
      match next.2 with
      | .err error => (next.1, .err error)
      | .val values => (next.1, .err (.raise (headValue values)))
    | .handle _ body rows =>
      let next := fixClock state (evaluate env state [body])
      match next.2 with
      | .err (.raise value) => match _selected : selectRow next.1 rows value value with
        | .error error => (next.1, .err error)
        | .ok (bindings, body) => evaluate { env with v := bindings ++ env.v } next.1 [body]
      | result => (next.1, result)
    | .con _ constructor args =>
      let next := evaluate env state args.reverse
      match next.2 with
      | .err error => (next.1, .err error)
      | .val values => (next.1, .val [.conv constructor values.reverse])
    | .app _ op args =>
      let next := fixClock state (evaluate env state args.reverse)
      match next.2 with
      | .err error => (next.1, .err error)
      | .val values => match op with
        | .src .opapp => match doOpApp values.reverse with
          | none => typeError next.1
          | some (newEnv, body) =>
            if next.1.clock = 0 then timeoutError next.1
            else evaluate newEnv (decClock next.1) [body]
        | .src .eval => match doEval values.reverse next.1.evalConfig with
          | none => typeError next.1
          | some (decs, config, result) =>
            let updated := { next.1 with evalConfig := config }
            if updated.clock = 0 then timeoutError updated else
            let last := evaluateDecs (decClock updated) decs
            match last.2 with
            | none => (last.1, .val [result])
            | some error => (last.1, .err error)
        | .src (.thunkOp .forceThunk) => match destThunk values next.1.refs with
          | .badRef | .notThunk => typeError next.1
          | .isThunk .evaluated value => (next.1, .val [value])
          | .isThunk .notEvaluated value =>
            let name := ofString "f"
            let last := evaluate ⟨[(name, value)]⟩ next.1 [appUnit (.varLocal .none name)]
            match last.2 with
            | .err error => (last.1, .err error)
            | .val values' => match updateThunk values last.1.refs values' with
              | none => typeError last.1
              | some refs => ({ last.1 with refs := refs }, .val values')
        | _ => applyResult next.1 op values.reverse
    | .if_ _ cond yes no =>
      let next := fixClock state (evaluate env state [cond])
      match next.2 with
      | .err error => (next.1, .err error)
      | .val values => match _selected : doIf (headValue values) yes no with
        | none => typeError next.1
        | some body => evaluate env next.1 [body]
    | .mat _ body rows =>
      let next := fixClock state (evaluate env state [body])
      match next.2 with
      | .err error => (next.1, .err error)
      | .val values => match _selected : selectRow next.1 rows (headValue values) bindExnV with
        | .error error => (next.1, .err error)
        | .ok (bindings, body) => evaluate { env with v := bindings ++ env.v } next.1 [body]
    | .let_ _ name first body =>
      let next := fixClock state (evaluate env state [first])
      match next.2 with
      | .err error => (next.1, .err error)
      | .val values =>
        let bindings := match name with | none => env.v | some name => (name, headValue values) :: env.v
        evaluate { env with v := bindings } next.1 [body]
    | .letrec _ funs body =>
      if (funs.map Prod.fst).Nodup then
        evaluate { env with v := buildRecEnv funs env env.v } state [body]
      else typeError state
termination_by (state.clock, expsWeight expressions)
decreasing_by
  all_goals simp_wf
  all_goals try simp_all only [expsWeight_reverse]
  all_goals try simp only [Prod.lex_def, expsWeight, expWeight, fixClock, decClock]
  all_goals try (have := expWeight_pos second)
  all_goals try (have _h := doIf_selected _ _ _ _ (by assumption); rcases _h with _h | _h <;> subst_vars)
  all_goals try (have _h := selectRow_weight _ _ _ _ _ _ (by assumption))
  all_goals try (have _h := appUnit_force_weight _ _)
  all_goals try dsimp only [updated] at *
  all_goals try dsimp only [next] at *
  all_goals try dsimp only [firstResult] at *
  all_goals try simp_all only [fixClock, appUnit, expWeight, expsWeight, Nat.lt_irrefl, false_or, true_and]
  all_goals try simp_all
  all_goals try omega

/-- Evaluate a list of flat declarations using the original clock. -/
noncomputable def evaluateDecs {C F : Type} (state : State C F) (declarations : List FlatLang.Exp) :
    State C F × Option (ErrorResult Value) :=
  match declarations with
  | [] => (state, none)
  | declaration :: rest =>
    let next := fixClock state (evaluate ⟨[]⟩ state [declaration])
    match next.2 with
    | .err error => (next.1, some error)
    | .val [.conv none []] => evaluateDecs next.1 rest
    | .val _ => (next.1, some (.abort .typeError))
termination_by (state.clock, expsWeight declarations + 1)
decreasing_by
  all_goals simp_wf
  all_goals simp only [Prod.lex_def, expsWeight, fixClock]
  all_goals try (have := expWeight_pos declaration)
  all_goals try dsimp only [next] at *
  all_goals try simp_all only [Nat.lt_irrefl, false_or, true_and]
  all_goals omega
end

end Flapjack.Compiler.Backend.FlatSem
