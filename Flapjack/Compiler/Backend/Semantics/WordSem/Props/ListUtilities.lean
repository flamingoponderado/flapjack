module

public import Flapjack.HolRef

@[expose] public section

/-!
# wordProps head-of-script list utilities

Counterpart of the `TODO move` list lemma `PERM_ALL_DISTINCT_MAP` at
`cakeml/compiler/backend/semantics/wordPropsScript.sml:62`. HOL's `PERM` is
`List.Perm`, `ALL_DISTINCT` is `List.Nodup`, `MAP` is `List.map` and `MEM` is
list membership.
-/

namespace Flapjack

/-- HOL `PERM_ALL_DISTINCT_MAP`: a permutation carries distinctness of a mapped
list across, and preserves membership. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "PERM_ALL_DISTINCT_MAP"]
theorem permAllDistinctMap {α β : Type} (f : α → β) :
    ∀ xs ys : List α, xs.Perm ys → (xs.map f).Nodup →
      (ys.map f).Nodup ∧ ∀ x, x ∈ ys ↔ x ∈ xs := by
  intro xs ys perm nodup
  exact ⟨(perm.map f).nodup_iff.mp nodup, fun x => perm.mem_iff.symm⟩

end Flapjack
