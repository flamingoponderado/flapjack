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
        | other => other
      | other => other :=
  BviSem.evaluateCons expression expressions env state

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
        | other => other
      | other => other :=
  BviSem.evaluateAppend first env state second

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
        | other => other
      | other => other :=
  BviSem.evaluateSnoc expressions env state expression

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
