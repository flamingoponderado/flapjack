import Flapjack.Misc.BalancedMap.InvariantSemantics
import Flapjack.Misc.BalancedMap.StructuralSize
import Flapjack.FiniteMap.CardinalityExact

namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison

/-- Full cardinality induction under the original comparator and invariant
premises. The canonical producer observation qualifier records only finite-map representation; cardinality is the size of the actual defined lookup domain, as HOL FCARD = CARD o FDOM, independently of the support witness. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "structure_size_to_fmap"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem structureSizeToFmap {κ ν : Type} (cmp : κ → κ → Ordering)
    (tree : Map κ ν) (hgood : goodCmp cmp) (hinv : invariant cmp tree) :
    (Flapjack.Misc.BalancedMap.toFmap cmp tree).card = structureSize tree := by
  classical
  induction tree with
  | tip => simp [toFmap, structureSize]
  | bin n key value left right ihleft ihright =>
    rcases (invariantEq (β := ν) cmp n key value left right).2.mp hinv with
      ⟨hdisj, hleftAbsent, hrightAbsent, _, _, _, _, hleft, hright⟩
    have hfresh : ((toFmap cmp left).union (toFmap cmp right)).lookup
        (keySet cmp key) = none := by
      by_contra h
      rcases (HolFiniteMapExact.union_defined_iff _ _ _).mp h with hl | hr
      · exact hleftAbsent hgood hl
      · exact hrightAbsent hgood hr
    rw [toFmap, HolFiniteMapExact.card_updateEq_fresh _ _ _ hfresh,
      HolFiniteMapExact.card_union_disjoint _ _ (hdisj hgood),
      ihleft hleft, ihright hright]
    simp only [structureSize]
    omega

/-- Original size/cardinality result assembled from structural size and the
full semantic-domain induction. The same actual-domain FCARD translation is used; no finite-key or cardinality premise is added. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "size_thm"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem sizeThm {κ ν : Type} (cmp : κ → κ → Ordering) (tree : Map κ ν)
    (hgood : goodCmp cmp) (hinv : invariant cmp tree) :
    size tree = (Flapjack.Misc.BalancedMap.toFmap cmp tree).card := by
  rw [structureSizeThm cmp tree hinv, structureSizeToFmap cmp tree hgood hinv]
end Flapjack.Misc.BalancedMap
