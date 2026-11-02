import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateClock

/-! Source-shaped clauses and clock properties of the flat evaluator. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Basis.Pure.MlString

/-- The empty expression-list case of the source evaluator. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluate_nil_source {C F : Type} (env : Environment Value) (state : State C F) :
    evaluate env state [] = (state, .val []) := by
  rw [evaluate]

/-- A list of at least two expressions clamps the first result's clock before
continuing and uses the original total head operation. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluate_cons_cons_source {C F : Type} (env : Environment Value) (state : State C F)
    (first second : FlatLang.Exp) (rest : List FlatLang.Exp) :
    evaluate env state (first :: second :: rest) =
      match fixClock state (evaluate env state [first]) with
      | (next, .err error) => (next, .err error)
      | (next, .val values) => match evaluate env next (second :: rest) with
        | (last, .err error) => (last, .err error)
        | (last, .val tail) => (last, .val (@Flapjack.holHd Value ⟨unitValue⟩ values :: tail)) := by
  rw [evaluate]
  generalize fixClock state (evaluate env state [first]) = result
  obtain ⟨next, result⟩ := result
  cases result with
  | err error => rfl
  | val values =>
    dsimp only
    generalize evaluate env next (second :: rest) = result
    obtain ⟨last, result⟩ := result
    cases result <;> rfl

/-- A literal returns its corresponding singleton flat value. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluate_lit_source {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (literal : Lit) :
    evaluate env state [.lit trace literal] = (state, .val [.litv literal]) := by
  rw [evaluate]

/-- Local variable lookup returns the first matching binding or a type error. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluate_varLocal_source {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (name : VarN) :
    evaluate env state [.varLocal trace name] =
      (state, match env.v.lookup name with
        | some value => .val [value]
        | none => .err (.abort .typeError)) := by
  rw [evaluate]
  cases env.v.lookup name <;> rfl

/-- A function captures its current flat environment. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluate_fn_source {C F : Type} (env : Environment Value) (state : State C F)
    (trace name : VarN) (body : FlatLang.Exp) :
    evaluate env state [.fn trace name body] = (state, .val [.closure env name body]) := by
  rw [evaluate]

/-- Raise evaluates its operand and propagates errors, using HOL's total HD. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluate_raise_source {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (body : FlatLang.Exp) :
    evaluate env state [.raise trace body] =
      match evaluate env state [body] with
      | (next, .val values) => (next, .err (.raise (@Flapjack.holHd Value ⟨unitValue⟩ values)))
      | (next, .err error) => (next, .err error) := by
  rw [evaluate]
  generalize evaluate env state [body] = result
  obtain ⟨next, result⟩ := result
  cases result <;> rfl

/-- Constructors evaluate their arguments in reverse order and restore the
original order in the resulting value. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluate_con_source {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (constructor : Option (FlatLang.CtorId × FlatLang.TypeId))
    (args : List FlatLang.Exp) :
    evaluate env state [.con trace constructor args] =
      match evaluate env state args.reverse with
      | (next, .val values) => (next, .val [.conv constructor values.reverse])
      | (next, .err error) => (next, .err error) := by
  rw [evaluate]
  generalize evaluate env state args.reverse = result
  obtain ⟨next, result⟩ := result
  cases result <;> rfl

/-- A let expression evaluates its body in the optional extended environment
after clamping the first expression's clock. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluate_let_source {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (name : Option VarN) (first body : FlatLang.Exp) :
    evaluate env state [.let_ trace name first body] =
      match fixClock state (evaluate env state [first]) with
      | (next, .err error) => (next, .err error)
      | (next, .val values) =>
        evaluate { env with v := match name with
          | none => env.v
          | some n => (n, @Flapjack.holHd Value ⟨unitValue⟩ values) :: env.v } next [body] := by
  rw [evaluate]
  generalize fixClock state (evaluate env state [first]) = result
  obtain ⟨next, result⟩ := result
  cases result <;> rfl

/-- A conditional checks the clamped condition value using `doIf`. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluate_if_source {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (condition yes no : FlatLang.Exp) :
    evaluate env state [.if_ trace condition yes no] =
      match fixClock state (evaluate env state [condition]) with
      | (next, .err error) => (next, .err error)
      | (next, .val values) => match doIf (@Flapjack.holHd Value ⟨unitValue⟩ values) yes no with
        | none => (next, .err (.abort .typeError))
        | some body => evaluate env next [body] := by
  rw [evaluate]
  generalize fixClock state (evaluate env state [condition]) = result
  obtain ⟨next, result⟩ := result
  cases result with
  | err error => rfl
  | val values =>
    simp only [headValue_eq_holHd]
    split <;> simp_all

/-- A handler examines rows only for a raised exception and retains the
original exception when no row matches. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluate_handle_source {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (body : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    evaluate env state [.handle trace body rows] =
      match fixClock state (evaluate env state [body]) with
      | (next, .err (.raise value)) => match pmatchRows rows next value with
        | .typeError => (next, .err (.abort .typeError))
        | .noMatch => (next, .err (.raise value))
        | .match (bindings, pattern, expression) =>
          if (FlatLang.patBindings pattern).Nodup then
            evaluate { env with v := bindings ++ env.v } next [expression]
          else (next, .err (.abort .typeError))
      | (next, result) => (next, result) := by
  rw [evaluate]
  generalize fixClock state (evaluate env state [body]) = result
  obtain ⟨next, result⟩ := result
  cases result with
  | val values => rfl
  | err error =>
    cases error with
    | abort error => rfl
    | raise value =>
      dsimp only
      unfold selectRow
      split <;> try simp_all
      all_goals split <;> simp_all
      all_goals split at * <;> simp_all

/-- Pattern matching raises the binding exception when no row matches and
rejects duplicate names in a selected pattern. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluate_mat_source {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (body : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    evaluate env state [.mat trace body rows] =
      match fixClock state (evaluate env state [body]) with
      | (next, .err error) => (next, .err error)
      | (next, .val values) => match pmatchRows rows next (@Flapjack.holHd Value ⟨unitValue⟩ values) with
        | .typeError => (next, .err (.abort .typeError))
        | .noMatch => (next, .err (.raise bindExnV))
        | .match (bindings, pattern, expression) =>
          if (FlatLang.patBindings pattern).Nodup then
            evaluate { env with v := bindings ++ env.v } next [expression]
          else (next, .err (.abort .typeError)) := by
  rw [evaluate]
  generalize fixClock state (evaluate env state [body]) = result
  obtain ⟨next, result⟩ := result
  cases result with
  | err error => rfl
  | val values =>
    dsimp only
    simp only [headValue_eq_holHd]
    unfold selectRow
    split <;> try simp_all
    all_goals split <;> simp_all
    all_goals split at * <;> simp_all

/-- Application evaluates arguments in reverse order, clamps the clock, and
dispatches calls, dynamic evaluation, thunk forcing and other primitives. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluate_app_source {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (op : FlatLang.Op) (args : List FlatLang.Exp) :
    evaluate env state [.app trace op args] =
      match fixClock state (evaluate env state args.reverse) with
      | (next, .err error) => (next, .err error)
      | (next, .val values) => match op with
        | .src .opapp => match doOpApp values.reverse with
          | none => (next, .err (.abort .typeError))
          | some (newEnv, body) =>
            if next.clock = 0 then (next, .err (.abort .timeoutError))
            else evaluate newEnv (decClock next) [body]
        | .src .eval => match doEval values.reverse next.evalConfig with
          | none => (next, .err (.abort .typeError))
          | some (decs, config, result) =>
            let updated := { next with evalConfig := config }
            if updated.clock = 0 then (updated, .err (.abort .timeoutError)) else
            match evaluateDecs (decClock updated) decs with
            | (last, none) => (last, .val [result])
            | (last, some error) => (last, .err error)
        | .src (.thunkOp .forceThunk) => match destThunk values next.refs with
          | .badRef | .notThunk => (next, .err (.abort .typeError))
          | .isThunk .evaluated value => (next, .val [value])
          | .isThunk .notEvaluated value =>
            let name := ofString "f"
            match evaluate ⟨[(name, value)]⟩ next [appUnit (.varLocal .none name)] with
            | (last, .err error) => (last, .err error)
            | (last, .val results) => match updateThunk values last.refs results with
              | none => (last, .err (.abort .typeError))
              | some refs => ({ last with refs := refs }, .val results)
        | _ => match doApp next op values.reverse with
          | none => (next, .err (.abort .typeError))
          | some (last, .err error) => (last, .err error)
          | some (last, .val value) => (last, .val [value]) := by
  rw [evaluate]
  generalize fixClock state (evaluate env state args.reverse) = result
  obtain ⟨next, result⟩ := result
  cases result with
  | err error => rfl
  | val values =>
    dsimp only
    cases op <;> try (rename_i source; cases source) <;>
      simp [applyResult]
    all_goals repeat' first | split at * | simp_all [applyResult]

/-- Recursive bindings reject duplicate function names. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluate_letrec_source {C F : Type} (env : Environment Value) (state : State C F)
    (trace : VarN) (funs : List (VarN × VarN × FlatLang.Exp)) (body : FlatLang.Exp) :
    evaluate env state [.letrec trace funs body] =
      if (funs.map Prod.fst).Nodup then
        evaluate { env with v := buildRecEnv funs env env.v } state [body]
      else (state, .err (.abort .typeError)) := by
  rw [evaluate]
  split <;> simp_all

/-- The empty declaration-list case of the source evaluator. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluateDecs_nil_source {C F : Type} (state : State C F) :
    evaluateDecs state [] = (state, none) := by
  rw [evaluateDecs]

/-- Declaration lists apply the source clock clamp before continuing. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluateDecs_cons_source {C F : Type} (state : State C F)
    (declaration : FlatLang.Exp) (rest : List FlatLang.Exp) :
    evaluateDecs state (declaration :: rest) =
      match fixClock state (evaluateDec state declaration) with
      | (next, none) => evaluateDecs next rest
      | (next, some error) => (next, some error) := by
  rw [(fixClock_evaluations ⟨[]⟩ state [declaration] declaration rest).2.1]
  exact evaluateDecs_cons state declaration rest

open Classical in
/-- A declaration succeeds precisely when its expression returns unit. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluateDec_source {C F : Type} (state : State C F) (declaration : FlatLang.Exp) :
    evaluateDec state declaration =
      match evaluate ⟨[]⟩ state [declaration] with
      | (next, .val values) =>
          if values = [unitValue] then (next, none) else (next, some (.abort .typeError))
      | (next, .err error) => (next, some error) := by
  unfold evaluateDec
  generalize evaluate ⟨[]⟩ state [declaration] = evaluated
  obtain ⟨next, result⟩ := evaluated
  cases result with
  | err error => rfl
  | val values =>
    dsimp only
    split <;> simp_all [unitValue]

/-- Expression, single-declaration and declaration-list evaluation do not
increase the clock. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_clock"]
theorem evaluate_clock_source {C F : Type} :
    (∀ (env : Environment Value) (state : State C F) (expressions : List FlatLang.Exp)
      (result : Result (List Value) Value) (next : State C F),
      evaluate env state expressions = (next, result) → next.clock ≤ state.clock) ∧
    (∀ (state : State C F) (declaration : FlatLang.Exp) (result : Option (ErrorResult Value))
      (next : State C F), evaluateDec state declaration = (next, result) → next.clock ≤ state.clock) ∧
    (∀ (state : State C F) (declarations : List FlatLang.Exp) (result : Option (ErrorResult Value))
      (next : State C F), evaluateDecs state declarations = (next, result) → next.clock ≤ state.clock) := by
  refine ⟨?_, ?_, ?_⟩
  · intro env state expressions result next run
    exact evaluate_clock_spec.1 env state next expressions result run
  · intro state declaration result next run
    exact evaluate_clock_spec.2.1 state next declaration result run
  · intro state declarations result next run
    exact evaluate_clock_spec.2.2 state next declarations result run

/-- Clock clamping leaves each kind of completed evaluation unchanged. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "fix_clock_evaluate"]
theorem fixClock_evaluations_source {C F : Type} (env : Environment Value) (state : State C F)
    (expressions : List FlatLang.Exp) (declaration : FlatLang.Exp) (declarations : List FlatLang.Exp) :
    fixClock state (evaluate env state expressions) = evaluate env state expressions ∧
    fixClock state (evaluateDec state declaration) = evaluateDec state declaration ∧
    fixClock state (evaluateDecs state declarations) = evaluateDecs state declarations :=
  fixClock_evaluations env state expressions declaration declarations

end Flapjack.Compiler.Backend.FlatSem
