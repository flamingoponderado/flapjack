import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateLength

/-! Successful result lengths for the clocked flat evaluator. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem

/-- Successful evaluation produces one value per expression. The evaluator and
its carriers remain pending complete HOL correspondence review.

HOL proves this in nine lines with `ho_match_mp_tac` on its generated
`evaluate_ind`, followed by `srw_tac`/`every_case_tac`. Lean has no direct
analogue: it cannot derive the functional induction principle for the mutual
well-founded `evaluate`/`evaluateDecs` definition (deriving `evaluate.induct`
fails inside `foldAndCollect`), so the case analysis has to be replayed over
the clock/weight measure. That measure induction is
`FlatSem.evaluate_singleton_length`, and `FlatSem.evaluate_length` derives the
list-length statement from it by list induction; this port reuses that proof
instead of duplicating it. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_length"]
theorem evaluate_length {C F : Type} :
    ∀ (env : Environment Value) (state next : State C F) (expressions : List FlatLang.Exp)
      (values : List Value), evaluate env state expressions = (next, .val values) →
      values.length = expressions.length :=
  FlatSem.evaluate_length

/-- Successful singleton evaluation returns exactly one value. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_sing"]
theorem evaluate_sing {C F : Type} (env : Environment Value) (state next : State C F)
    (expression : FlatLang.Exp) (values : List Value)
    (run : evaluate env state [expression] = (next, .val values)) :
    ∃ value, values = [value] := by
  have length := evaluate_length env state next [expression] values run
  cases values with
  | nil => simp at length
  | cons value rest =>
    cases rest with
    | nil => exact ⟨value, rfl⟩
    | cons other rest => simp at length

end Flapjack.Compiler.Backend.FlatProps
