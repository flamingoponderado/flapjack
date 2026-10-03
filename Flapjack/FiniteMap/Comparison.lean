import Flapjack.FiniteMap.Toto

namespace Flapjack.FiniteMap.Comparison

/-- Literal HOL comparator predicate. Equal may identify distinct keys; no
antisymmetry of key equality or total-order typeclass is imposed. The seven
universally quantified clauses retain their original order and directions. -/
@[hol "HOL/src/finite_maps/comparisonScript.sml" "good_cmp_def"]
def goodCmp {κ : Type} (cmp : κ → κ → Ordering) : Prop :=
  (∀ x, cmp x x = .eq) ∧
  (∀ x y, cmp x y = .eq → cmp y x = .eq) ∧
  (∀ x y, cmp x y = .gt ↔ cmp y x = .lt) ∧
  (∀ x y z, cmp x y = .eq ∧ cmp y z = .lt → cmp x z = .lt) ∧
  (∀ x y z, cmp x y = .lt ∧ cmp y z = .eq → cmp x z = .lt) ∧
  (∀ x y z, cmp x y = .eq ∧ cmp y z = .eq → cmp x z = .eq) ∧
  (∀ x y z, cmp x y = .lt ∧ cmp y z = .lt → cmp x z = .lt)

/-- Original implication for an arbitrary comparator and arbitrary key type.
All seven good_cmp clauses are derived from the three original TotOrd clauses. -/
@[hol "HOL/src/finite_maps/comparisonScript.sml" "TotOrder_imp_good_cmp"]
theorem totOrderImpGoodCmp {α : Type} (comparison : α → α → Ordering)
    (ordered : Flapjack.FiniteMap.Toto.totOrd comparison) : goodCmp comparison := by
  refine ⟨?_, ?_, ordered.2.1, ?_, ?_, ?_, ordered.2.2⟩
  · intro x
    exact (ordered.1 x x).mpr rfl
  · intro x y same
    exact (ordered.1 y x).mpr ((ordered.1 x y).mp same).symm
  · intro x y z premises
    have same := (ordered.1 x y).mp premises.1
    subst y
    exact premises.2
  · intro x y z premises
    have same := (ordered.1 y z).mp premises.2
    subst z
    exact premises.1
  · intro x y z premises
    exact (ordered.1 x z).mpr (((ordered.1 x y).mp premises.1).trans
      ((ordered.1 y z).mp premises.2))

end Flapjack.FiniteMap.Comparison
