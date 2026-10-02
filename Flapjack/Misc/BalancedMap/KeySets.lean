import Flapjack.Misc.BalancedMap.Semantics
import Flapjack.FiniteMap.Comparison
import Mathlib.Data.Set.Lattice

namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "key_set_equiv"]
theorem keySetEquiv {κ : Type} (cmp : κ → κ → Ordering) (h : goodCmp cmp) :
    (∀ key, key ∈ keySet cmp key) ∧
    (∀ k1 k2, k1 ∈ keySet cmp k2 → k2 ∈ keySet cmp k1) ∧
    (∀ k1 k2 k3, k1 ∈ keySet cmp k2 ∧ k2 ∈ keySet cmp k3 → k1 ∈ keySet cmp k3) := by
  rcases h with ⟨hrefl, hsym, _, _, _, htrans, _⟩
  refine ⟨hrefl, ?_, ?_⟩
  · intro k1 k2 hmem
    exact hsym k2 k1 hmem
  · intro k1 k2 k3 hmem
    exact htrans k3 k2 k1 ⟨hmem.2, hmem.1⟩

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "key_set_nonempty"]
theorem keySetNonempty {κ : Type} (cmp : κ → κ → Ordering) (key : κ)
    (h : goodCmp cmp) : keySet cmp key ≠ ∅ := by
  intro hempty
  have hmem := (keySetEquiv cmp h).1 key
  rw [hempty] at hmem
  exact hmem

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "key_set_eq"]
theorem keySetEq {κ : Type} (cmp : κ → κ → Ordering) (k1 k2 : κ)
    (h : goodCmp cmp) : keySet cmp k1 = keySet cmp k2 ↔ cmp k1 k2 = .eq := by
  rcases h with ⟨hrefl, hsym, _, _, _, htrans, _⟩
  constructor
  · intro heq
    have hmem : k2 ∈ keySet cmp k2 := hrefl k2
    rw [← heq] at hmem
    exact hmem
  · intro heq
    ext query
    constructor
    · intro hmem
      exact htrans k2 k1 query ⟨hsym k1 k2 heq, hmem⟩
    · intro hmem
      exact htrans k1 k2 query ⟨heq, hmem⟩

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "key_set_partition"]
theorem keySetPartition {κ : Type} (cmp : κ → κ → Ordering) (k1 k2 : κ)
    (h : goodCmp cmp ∧ keySet cmp k1 ≠ keySet cmp k2) :
    Disjoint (keySet cmp k1) (keySet cmp k2) := by
  apply Set.disjoint_left.mpr
  intro query hleft hright
  apply h.2
  apply (keySetEq cmp k1 k2 h.1).mpr
  rcases h.1 with ⟨_, hsym, _, _, _, htrans, _⟩
  exact htrans k1 query k2 ⟨hleft, hsym k2 query hright⟩

end Flapjack.Misc.BalancedMap
