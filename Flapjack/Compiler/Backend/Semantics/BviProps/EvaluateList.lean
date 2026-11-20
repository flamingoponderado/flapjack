module

public import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateList
public import Flapjack.Misc.ListEl
public import Flapjack.HolRef

@[expose] public section

/-!
# List lemmas of HOL `bviProps`

Counterpart of `cakeml/compiler/backend/semantics/bviPropsScript.sml:646-665`:
`take_drop_lem`, the BVI twin of the `bvlProps` list lemma.
-/

namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value unitValue)

namespace ListCarrier
/-- Canonical BVI reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BviSem.BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end ListCarrier

/-- Flapjack helper comparing the catch-all result case with HOL's explicit
    `Rerr` arm. It has no separate HOL declaration: HOL writes the error arms
    out inline in `evaluate_CONS`, `evaluate_APPEND` and `evaluate_SNOC`. -/
private theorem evalTupleCaseEq {C F : Type} (run : EvalResult C F)
    (head : List Value → BviState C F → EvalResult C F) :
    (match run with
      | (.val values, n) => head values n
      | other => other) =
    (match run with
      | (.val values, n) => head values n
      | (.err e, s1) => (.err e, s1)) := by
  obtain ⟨result, next⟩ := run
  cases result with
  | err error => rfl
  | val values => rfl

/-- Flapjack helper for the two-level case in `evaluate_CONS`: the two heads
    agree pointwise, so the catch-all and explicit-arm forms coincide. -/
private theorem evalTupleCaseEqHeads {C F : Type} (run : EvalResult C F)
    (headL headR : List Value → BviState C F → EvalResult C F)
    (hhead : ∀ values n, headL values n = headR values n) :
    (match run with
      | (.val values, n) => headL values n
      | other => other) =
    (match run with
      | (.val values, n) => headR values n
      | (.err e, s1) => (.err e, s1)) := by
  obtain ⟨result, next⟩ := run
  cases result with
  | err error => rfl
  | val values => exact hhead values next

/-- Evaluate a nonempty list by evaluating its head then its tail. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "evaluate_CONS"
  (fmap_as_finite_support := [refs])]
theorem evaluateCons {C F : Type} (expression : Bvi.Exp) (expressions : List Bvi.Exp)
    (env : List Value) (state : Flapjack.Compiler.Backend.BviSem.BviState C F) :
    evaluateTuple (expression :: expressions, env, state) =
      match evaluateTuple ([expression], env, state) with
      | (.val values, next) =>
        match evaluateTuple (expressions, env, next) with
        | (.val tail, last) => (.val (@Flapjack.holHd Value ⟨unitValue⟩ values :: tail), last)
        | (.err e, s1) => (.err e, s1)
      | (.err e, s2) => (.err e, s2) := by
  rw [BviSem.evaluateCons]
  refine evalTupleCaseEqHeads (evaluateTuple ([expression], env, state)) _ _ ?_
  intro values n
  exact evalTupleCaseEq (evaluateTuple (expressions, env, n)) (fun t l =>
    (.val (@Flapjack.holHd Value ⟨unitValue⟩ values :: t), l))

/-- Evaluate an append by evaluating the two lists in order. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "evaluate_APPEND"
  (fmap_as_finite_support := [refs])]
theorem evaluateAppend {C F : Type} (first : List Bvi.Exp) (env : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F) (second : List Bvi.Exp) :
    evaluateTuple (first ++ second, env, state) =
      match evaluateTuple (first, env, state) with
      | (.val values, next) =>
        match evaluateTuple (second, env, next) with
        | (.val tail, last) => (.val (values ++ tail), last)
        | (.err e, s1) => (.err e, s1)
      | (.err e, s2) => (.err e, s2) := by
  rw [BviSem.evaluateAppend]
  refine evalTupleCaseEqHeads (evaluateTuple (first, env, state)) _ _ ?_
  intro values n
  exact evalTupleCaseEq (evaluateTuple (second, env, n)) (fun tail last =>
    (.val (values ++ tail), last))

/-- Evaluate a list with one expression appended at the end. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "evaluate_SNOC"
  (fmap_as_finite_support := [refs])]
theorem evaluateSnoc {C F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F) (expression : Bvi.Exp) :
    evaluateTuple (expressions ++ [expression], env, state) =
      match evaluateTuple (expressions, env, state) with
      | (.val values, next) =>
        match evaluateTuple ([expression], env, next) with
        | (.val tail, last) => (.val (values ++ tail), last)
        | (.err e, s1) => (.err e, s1)
      | (.err e, s2) => (.err e, s2) := by
  rw [BviSem.evaluateSnoc]
  refine evalTupleCaseEqHeads (evaluateTuple (expressions, env, state)) _ _ ?_
  intro values n
  exact evalTupleCaseEq (evaluateTuple ([expression], env, n)) (fun tail last =>
    (.val (values ++ tail), last))

/-- A dropped prefix splits into its head and the rest of the drop. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "take_drop_lem"
  (total_function_inhabitants := [α])]
theorem takeDropLem {α : Type} [Nonempty α] (skip : Nat) (env : List α) (n : Nat)
    (bounds : skip < env.length ∧ skip + (n + 1) ≤ env.length ∧ env.drop skip ≠ []) :
    Flapjack.holEl skip env :: (env.drop (1 + skip)).take n =
      (env.drop skip).take (n + 1) := by
  obtain ⟨short, _long, _nonempty⟩ := bounds
  rw [Flapjack.holEl_eq_getElem skip env short]
  rw [List.drop_eq_getElem_cons short, List.take_succ_cons]
  congr 1
  rw [Nat.add_comm]

end Flapjack.Compiler.Backend.BviProps
