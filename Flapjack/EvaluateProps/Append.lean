module

public import Flapjack.EvaluateProps.Length
public import Mathlib.Tactic.Conv

@[expose] public section

/-! Source evaluation over cons and appended expression lists. -/
namespace Flapjack.EvaluateProps
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.EvaluateHOL

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_cons"]
theorem evaluate_cons {σ : Type} (st : State σ) (env : SemEnv Value) (expr : AstHOL.Exp)
    (rest : List AstHOL.Exp) :
    evaluate st env (expr :: rest) =
      match evaluate st env [expr] with
      | (middle, .val values) =>
        match evaluate middle env rest with
        | (next, .val tail) => (next, .val (values ++ tail))
        | (next, .err error) => (next, .err error)
      | (middle, .err error) => (middle, .err error) := by
  cases rest with
  | nil =>
    cases h : evaluate st env [expr] with
    | mk middle result =>
      cases result with
      | err error => simp
      | val values => simp [evaluate]
  | cons second tail =>
    rw [evaluateConsSource]
    cases h : evaluate st env [expr] with
    | mk next result =>
      cases result with
      | err error => simp
      | val values =>
        obtain ⟨single, rfl⟩ := evaluateSingFull st env expr next values h
        cases h2 : evaluate next env (second :: tail) with
        | mk last result =>
          cases result with
          | err error => simp [h2]
          | val tailValues => simp [h2, headValue, holHd]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_append"]
theorem evaluate_append {σ : Type} (st : State σ) (env : SemEnv Value)
    (xs ys : List AstHOL.Exp) :
    evaluate st env (xs ++ ys) =
      match evaluate st env xs with
      | (middle, .val values) =>
        match evaluate middle env ys with
        | (next, .val tail) => (next, .val (values ++ tail))
        | (next, .err error) => (next, .err error)
      | (middle, .err error) => (middle, .err error) := by
  induction xs generalizing st with
  | nil =>
    cases h : evaluate st env ys with
    | mk next result =>
      cases result with
      | err error => simp [h, evaluate]
      | val values => simp [h, evaluate]
  | cons first rest ih =>
    conv_lhs => rw [List.cons_append, evaluate_cons]
    conv_rhs => rw [evaluate_cons]
    cases h : evaluate st env [first] with
    | mk middle result =>
      cases result with
      | err error => simp
      | val values =>
        cases h2 : evaluate middle env rest with
        | mk middle' restResult =>
          cases restResult with
          | err error => simp only [ih middle, h2]
          | val values' =>
            cases h3 : evaluate middle' env ys with
            | mk next ysResult =>
              cases ysResult with
              | err error => simp only [ih middle, h2, h3]
              | val tail => simp only [ih middle, h2, h3, List.append_assoc]

end Flapjack.EvaluateProps
