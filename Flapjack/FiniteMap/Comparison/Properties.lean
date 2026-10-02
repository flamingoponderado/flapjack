import Flapjack.FiniteMap.Comparison

namespace Flapjack.FiniteMap.Comparison

/-- Full original datatype/comparator bundle. The original LIST_CONJ shares
one carrier for case results and comparator keys; no law is strengthened. -/
@[hol "HOL/src/finite_maps/comparisonScript.sml" "cmp_thms"]
theorem cmpThms {κ : Type} :
    (Ordering.lt ≠ .eq ∧ Ordering.lt ≠ .gt ∧ Ordering.eq ≠ .gt) ∧
    ((∀ v0 v1 v2 : κ, (match Ordering.lt with
        | .lt => v0 | .eq => v1 | .gt => v2) = v0) ∧
     (∀ v0 v1 v2 : κ, (match Ordering.eq with
        | .lt => v0 | .eq => v1 | .gt => v2) = v1) ∧
     (∀ v0 v1 v2 : κ, (match Ordering.gt with
        | .lt => v0 | .eq => v1 | .gt => v2) = v2)) ∧
    (∀ a : Ordering, a = .lt ∨ a = .eq ∨ a = .gt) ∧
    (∀ cmp : κ → κ → Ordering, goodCmp cmp ↔
      (∀ x, cmp x x = .eq) ∧
      (∀ x y, cmp x y = .eq → cmp y x = .eq) ∧
      (∀ x y, cmp x y = .gt ↔ cmp y x = .lt) ∧
      (∀ x y z, cmp x y = .eq ∧ cmp y z = .lt → cmp x z = .lt) ∧
      (∀ x y z, cmp x y = .lt ∧ cmp y z = .eq → cmp x z = .lt) ∧
      (∀ x y z, cmp x y = .eq ∧ cmp y z = .eq → cmp x z = .eq) ∧
      (∀ x y z, cmp x y = .lt ∧ cmp y z = .lt → cmp x z = .lt)) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro a; cases a <;> simp
  · intro cmp; rfl

end Flapjack.FiniteMap.Comparison
