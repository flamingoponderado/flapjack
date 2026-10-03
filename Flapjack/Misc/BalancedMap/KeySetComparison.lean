import Flapjack.Misc.BalancedMap.Semantics
import Flapjack.FiniteMap.Comparison

namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "key_set_cmp_def"]
def keySetCmp {κ ι ρ : Type} (cmp : κ → ι → ρ) (key : κ) (keys : Set ι)
    (result : ρ) : Prop :=
  ∀ query, query ∈ keys → cmp key query = result

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "key_set_cmp_thm"]
theorem keySetCmpThm {κ : Type} (cmp : κ → κ → Ordering) (key key' : κ)
    (result : Ordering) (h : goodCmp cmp) :
    keySetCmp cmp key (keySet cmp key') result ↔ cmp key key' = result := by
  rcases h with ⟨hrefl, hsym, hswap, heqLt, hltEq, heqEq, _⟩
  constructor
  · intro hclass
    exact hclass key' (hrefl key')
  · intro hresult query hmem
    cases result with
    | lt => exact hltEq key key' query ⟨hresult, hmem⟩
    | eq => exact heqEq key key' query ⟨hresult, hmem⟩
    | gt =>
      apply (hswap key query).mpr
      exact heqLt query key' key ⟨hsym key' query hmem, (hswap key key').mp hresult⟩

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "key_set_cmp2_def"]
def keySetCmp2 {κ ι ρ : Type} (cmp : κ → ι → ρ) (left : Set κ) (right : Set ι)
    (result : ρ) : Prop :=
  ∀ k1 k2, k1 ∈ left ∧ k2 ∈ right → cmp k1 k2 = result

end Flapjack.Misc.BalancedMap
