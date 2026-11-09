import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateSource

/-! The flat pattern-match evaluator used by the source-to-flat proof. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

/-- Evaluate the selected flat match row or return the corresponding match error. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_match_def"]
noncomputable def evaluateMatch {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state : FlatSem.State C F) (value : FlatSem.Value)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (errorValue : FlatSem.Value) : FlatSem.EvalResult C F :=
  match FlatSem.pmatchRows rows state value with
  | .typeError => (state, .err (.abort .typeError))
  | .noMatch => (state, .err (.raise errorValue))
  | .match (bindings, pattern, body) =>
    if (FlatLang.patBindings pattern).Nodup then
      FlatSem.evaluate { env with v := bindings ++ env.v } state [body]
    else (state, .err (.abort .typeError))

open Flapjack.Compiler.Backend.FlatSem

/-- Matching an empty row list raises the supplied failure value. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_match_NIL"]
theorem evaluateMatch_nil {C F : Type} (env : Environment Value) (state : State C F) (v err : Value) :
    evaluateMatch env state v [] err = (state, .err (.raise err)) := by
  simp [evaluateMatch, pmatchRows]
open Classical in
/-- Matching a nonempty row list follows the first pattern and row-error checks. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_match_CONS"]
theorem evaluateMatch_cons {C F : Type} (env : Environment Value) (state : State C F) (v : Value)
    (p : FlatLang.Pat) (e : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp)) (err : Value) :
    evaluateMatch env state v ((p,e) :: rows) err =
      match pmatch state p v [] with
      | .noMatch => evaluateMatch env state v rows err
      | .typeError => (state, .err (.abort .typeError))
      | .match bindings =>
        if (FlatLang.patBindings p).Nodup ∧ pmatchRows rows state v ≠ .typeError then
          evaluate { env with v := bindings ++ env.v } state [e]
        else (state, .err (.abort .typeError)) := by
  classical
  unfold evaluateMatch
  rw [pmatchRows]
  cases head : pmatch state p v [] with
  | noMatch => rfl
  | typeError => rfl
  | «match» bindings =>
    cases rest : pmatchRows rows state v with
    | typeError => simp
    | noMatch => simp
    | «match» payload => simp

open Classical in
/-- A match expression delegates successful row selection to evaluateMatch. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_Mat"]
theorem evaluate_mat {C F : Type} (env : Environment Value) (state : State C F)
    (tra : Flapjack.Compiler.Backend.BackendCommon.Tra) (e : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    evaluate env state [.mat tra e rows] =
      match evaluate env state [e] with
      | (next, .val values) =>
        if pmatchRows rows next (@Flapjack.holHd Value ⟨unitValue⟩ values) ≠ .typeError then
          evaluateMatch env next (@Flapjack.holHd Value ⟨unitValue⟩ values) rows bindExnV
        else (next, .err (.abort .typeError))
      | result => result := by
  rw [evaluate_mat_source, (fixClock_evaluations env state [e] e []).1]
  cases evaluated : evaluate env state [e] with
  | mk next result =>
    cases result with
    | err error => rfl
    | val values =>
      cases matched : pmatchRows rows next (@Flapjack.holHd Value ⟨unitValue⟩ values) <;> simp [evaluateMatch, matched]

open Classical in
/-- An exception handler delegates a raised value to evaluateMatch. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_Handle"]
theorem evaluate_handle {C F : Type} (env : Environment Value) (state : State C F)
    (tra : Flapjack.Compiler.Backend.BackendCommon.Tra) (e : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    evaluate env state [.handle tra e rows] =
      match evaluate env state [e] with
      | (next, .err (.raise v)) =>
        if pmatchRows rows next v ≠ .typeError then evaluateMatch env next v rows v
        else (next, .err (.abort .typeError))
      | result => result := by
  rw [evaluate_handle_source, (fixClock_evaluations env state [e] e []).1]
  cases evaluated : evaluate env state [e] with
  | mk next result =>
    cases result with
    | val values => rfl
    | err error =>
      cases error with
      | abort error => rfl
      | raise value => cases matched : pmatchRows rows next value <;> simp [evaluateMatch, matched]
end Flapjack.Compiler.Backend.FlatProps
