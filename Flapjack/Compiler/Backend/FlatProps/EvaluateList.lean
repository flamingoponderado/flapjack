module

public import Flapjack.Compiler.Backend.FlatProps.EvaluateLength
public import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateSource

@[expose] public section
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem
/-- Evaluating a cons evaluates its head and tail in sequence, propagating errors. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_cons"]
theorem evaluate_cons {C F : Type} (env : Environment Value) (state : State C F) (e : FlatLang.Exp) (es : List FlatLang.Exp) :
    evaluate env state (e :: es) =
      match evaluate env state [e] with
      | (next, .val values) => match evaluate env next es with
        | (last, .val values') => (last, .val (values ++ values'))
        | result => result
      | result => result := by
  cases es with
  | nil =>
    cases run : evaluate env state [e] with
    | mk next result => cases result <;> simp [evaluate_nil_source]
  | cons second rest =>
    rw [evaluate_cons_cons_source, (fixClock_evaluations env state [e] e []).1]
    cases run : evaluate env state [e] with
    | mk next result =>
      cases result with
      | err error => rfl
      | val values =>
        obtain ⟨value, rfl⟩ := evaluate_sing env state e next values run
        cases tail : evaluate env next (second :: rest) with
        | mk last result => cases result <;> simp [tail, Flapjack.holHd]
/-- Evaluation of appended expression lists sequences both evaluations. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_append"]
theorem evaluate_append {C F : Type} (env : Environment Value) (state : State C F) (left right : List FlatLang.Exp) :
    evaluate env state (left ++ right) =
      match evaluate env state left with
      | (next, .val values) => match evaluate env next right with
        | (last, .val values') => (last, .val (values ++ values'))
        | result => result
      | result => result := by
  induction left generalizing state with
  | nil => simp [evaluate_nil_source]; cases evaluate env state right with | mk next result => cases result <;> rfl
  | cons e es ih =>
    rw [evaluate_cons env state e es]
    rw [List.cons_append, evaluate_cons]
    cases head : evaluate env state [e] with
    | mk next result =>
      cases result with
      | err error => rfl
      | val values =>
        dsimp only
        rw [ih]
        cases middle : evaluate env next es with
        | mk after result =>
          cases result with
          | err error => rfl
          | val tail =>
            cases last : evaluate env after right with
            | mk final result => cases result <;> simp [last, List.append_assoc]

end Flapjack.Compiler.Backend.FlatProps
