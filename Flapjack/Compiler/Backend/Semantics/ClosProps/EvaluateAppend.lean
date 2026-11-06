import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
import Flapjack.Misc.ListEl

/-! Sequencing properties of the clocked closure evaluator. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL

namespace EvaluateAppendPort
/-- Canonical closure-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end EvaluateAppendPort

/-- A successful evaluation returns one value per expression. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_IMP_LENGTH"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateImpLength {C F : Type} (xs : List ClosLang.Exp)
    (env : List ClosSem.Value) (s s1 : ClosSem.State C F) (values : List ClosSem.Value)
    (run : ClosSem.evaluate xs env s = (.val values, s1)) : xs.length = values.length :=
  (ClosSem.evaluate_length.1 xs env s s1 values run).symm

/-- A successful singleton evaluation returns a singleton list. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_SING"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateSing {C F : Type} (x : ClosLang.Exp) (env : List ClosSem.Value)
    (s s2 : ClosSem.State C F) (values : List ClosSem.Value)
    (run : ClosSem.evaluate [x] env s = (.val values, s2)) :
    ∃ value, values = [value] :=
  ClosSem.evaluate_singleton_value x env s s2 values run

/-- Evaluating a nonempty list sequences its head and tail. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_CONS"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateCons {C F : Type} (x : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env : List ClosSem.Value) (s : ClosSem.State C F) :
    ClosSem.evaluate (x :: xs) env s =
      match ClosSem.evaluate [x] env s with
      | (.val values, next) =>
        match ClosSem.evaluate xs env next with
        | (.val rest, last) => (.val (@Flapjack.holHd ClosSem.Value ⟨.number 0⟩ values :: rest), last)
        | (.err error, last) => (.err error, last)
      | (.err error, next) => (.err error, next) := by
  cases head : ClosSem.evaluate [x] env s with
  | mk result next =>
    cases result with
    | err error => simp [evaluate_cons_error x xs env s next error head]
    | val values =>
      obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value x env s next values head
      rw [evaluate_cons_value x xs env s next value head]
      cases tail : ClosSem.evaluate xs env next with
      | mk result last => cases result <;> simp [Flapjack.holHd, tail]

/-- Evaluation of an append first evaluates its left side, propagating errors. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_APPEND"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAppend {C F : Type} (xs ys : List ClosLang.Exp)
    (env : List ClosSem.Value) (s : ClosSem.State C F) :
    ClosSem.evaluate (xs ++ ys) env s =
      match ClosSem.evaluate xs env s with
      | (.val values, next) =>
        match ClosSem.evaluate ys env next with
        | (.val rest, last) => (.val (values ++ rest), last)
        | (.err error, last) => (.err error, last)
      | (.err error, next) => (.err error, next) := by
  induction xs generalizing s with
  | nil =>
    simp only [List.nil_append, ClosSem.evaluate]
    cases h : ClosSem.evaluate ys env s with
    | mk result last => cases result <;> rfl
  | cons x xs ih =>
    cases head : ClosSem.evaluate [x] env s with
    | mk result next =>
      cases result with
      | err error =>
        simp [evaluate_cons_error x (xs ++ ys) env s next error head,
          evaluate_cons_error x xs env s next error head]
      | val values =>
        obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value x env s next values head
        simp only [List.cons_append]
        rw [evaluate_cons_value x (xs ++ ys) env s next value head,
          evaluate_cons_value x xs env s next value head, ih]
        cases tail : ClosSem.evaluate xs env next with
        | mk result last =>
          cases result with
          | err error => simp
          | val values =>
            cases final : ClosSem.evaluate ys env last with
            | mk result finalState => cases result <;> simp [final]

/-- Evaluation of a snoc sequences the last expression after the prefix. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_SNOC"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateSnoc {C F : Type} (xs : List ClosLang.Exp) (env : List ClosSem.Value)
    (s : ClosSem.State C F) (x : ClosLang.Exp) :
    ClosSem.evaluate (xs ++ [x]) env s =
      match ClosSem.evaluate xs env s with
      | (.val values, next) =>
        match ClosSem.evaluate [x] env next with
        | (.val rest, last) => (.val (values ++ rest), last)
        | (.err error, last) => (.err error, last)
      | (.err error, next) => (.err error, next) :=
  evaluateAppend xs [x] env s

end Flapjack.Compiler.Backend.ClosProps
