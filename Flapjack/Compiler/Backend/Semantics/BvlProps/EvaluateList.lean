import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateLength
import Flapjack.HolRef

/-! Sequencing properties of BVL expression-list evaluation. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem

namespace ListCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end ListCarrier

/-- Evaluate a nonempty list by evaluating its head then its tail. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_CONS"
  (fmap_as_finite_support := [refs])]
theorem evaluateCons {C F : Type} (expression : Bvl.Exp) (expressions : List Bvl.Exp)
    (env : List Value) (state : Flapjack.Compiler.Backend.BvlSem.State C F) :
    evaluateTuple (expression :: expressions, env, state) =
      match evaluateTuple ([expression], env, state) with
      | (.val values, next) =>
        match evaluateTuple (expressions, env, next) with
        | (.val tail, last) => (.val (@Flapjack.holHd Value ⟨unitValue⟩ values :: tail), last)
        | other => other
      | other => other := by
  cases expressions with
  | nil =>
    cases run : evaluateTuple ([expression], env, state) with
    | mk result next =>
      cases result with
      | err error => simp
      | val values =>
        obtain ⟨value, rfl⟩ := evaluateSing expression env state values next run
        simp [evaluateTuple, evaluate, Flapjack.holHd]
  | cons second rest =>
    simp only [evaluateTuple]
    rw [evaluate, fixClock_evaluate]
    cases evaluate [expression] env state with
    | mk result next =>
      cases result with
      | err error => rfl
      | val values =>
        dsimp only
        cases evaluate (second :: rest) env next with
        | mk result last => cases result <;> rfl

/-- Evaluate an append by evaluating the two lists in order. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_APPEND"
  (fmap_as_finite_support := [refs])]
theorem evaluateAppend {C F : Type} (first : List Bvl.Exp) (env : List Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F) (second : List Bvl.Exp) :
    evaluateTuple (first ++ second, env, state) =
      match evaluateTuple (first, env, state) with
      | (.val values, next) =>
        match evaluateTuple (second, env, next) with
        | (.val tail, last) => (.val (values ++ tail), last)
        | other => other
      | other => other := by
  induction first generalizing state with
  | nil =>
    simp only [List.nil_append, evaluateTuple]
    rw [evaluate]
    dsimp only
    cases evaluate second env state with
    | mk result next => cases result <;> rfl
  | cons expression rest ih =>
    rw [List.cons_append, evaluateCons expression (rest ++ second) env state,
      evaluateCons expression rest env state]
    cases headRun : evaluateTuple ([expression], env, state) with
    | mk headResult next =>
      cases headResult with
      | err error => rfl
      | val values =>
        dsimp only
        rw [ih]
        cases tailRun : evaluateTuple (rest, env, next) with
        | mk tailResult last =>
          cases tailResult with
          | err error => rfl
          | val tail =>
            dsimp only
            cases evaluateTuple (second, env, last) with
            | mk result final => cases result <;> simp

/-- Evaluate a list with one expression appended at the end. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_SNOC"
  (fmap_as_finite_support := [refs])]
theorem evaluateSnoc {C F : Type} (expressions : List Bvl.Exp) (env : List Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F) (expression : Bvl.Exp) :
    evaluateTuple (expressions ++ [expression], env, state) =
      match evaluateTuple (expressions, env, state) with
      | (.val values, next) =>
        match evaluateTuple ([expression], env, next) with
        | (.val tail, last) => (.val (values ++ tail), last)
        | other => other
      | other => other :=
  evaluateAppend expressions env state [expression]

end Flapjack.Compiler.Backend.BvlProps
