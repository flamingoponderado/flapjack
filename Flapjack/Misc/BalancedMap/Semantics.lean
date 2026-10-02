import Flapjack.Misc.BalancedMap.Core
import Flapjack.FiniteMap.UnionExact
import Mathlib.Data.Set.Basic

namespace Flapjack.Misc.BalancedMap

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "key_set_def"]
def keySet {κ ι : Type} (cmp : κ → ι → Ordering) (key : κ) : Set ι :=
  {query | cmp key query = .eq}

/-- Literal semantic finite map: keys are comparator-equivalence sets, not
individual keys. Classical equality decides equality of these sets, as HOL's
finite-map update does. This proof-side definition does not replace the
production tree map. No comparator law or decidable set-equality premise is
added to the HOL definition. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "to_fmap_def"
  (fmap_as_finite_support_result)]
noncomputable def toFmap {κ ι ν : Type} (cmp : κ → ι → Ordering) :
    Map κ ν → HolFiniteMapExact (Set ι) ν
  | .tip => HolFiniteMapExact.empty
  | .bin _ key value left right => by
    classical
    exact ((toFmap cmp left).union (toFmap cmp right)).updateEq (keySet cmp key, value)

/-- Independent raw lookup codec for the HOL semantic equation. It does not
call the canonical map operation or assume the target correspondence; it
selects the root binding by set equality, then the left binding, then right.
This is Flapjack witness infrastructure without a separate HOL declaration. -/
noncomputable def semanticLookup {κ ι ν : Type} (cmp : κ → ι → Ordering) :
    Map κ ν → Set ι → Option ν
  | .tip, _ => none
  | .bin _ key value left right, query => by
    classical
    exact if query = keySet cmp key then some value else
      match semanticLookup cmp left query with
      | none => semanticLookup cmp right query
      | some found => some found

/-- Lookup-level carrier witness against the independent raw semantic codec;
it retains arbitrary comparators and malformed cached sizes. -/
theorem holFmapAsFiniteSupportResultWitness_toFmap {κ ι ν : Type}
    (cmp : κ → ι → Ordering) (tree : Map κ ν) (query : Set ι) :
    (toFmap cmp tree).lookup query = semanticLookup cmp tree query := by
  classical
  induction tree with
  | tip => rfl
  | bin n key value left right ihleft ihright =>
    simp only [toFmap, semanticLookup, HolFiniteMapExact.lookup_union,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ihleft, ihright]
    rfl

end Flapjack.Misc.BalancedMap
