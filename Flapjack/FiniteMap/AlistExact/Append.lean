module

public import Flapjack.FiniteMap.AlistExact
public import Flapjack.FiniteMap.UnionExact
public import Flapjack.FiniteMap.MapKeys

@[expose] public section

/-! Association-list append and left-biased finite-map union. -/
namespace Flapjack.HolFiniteMapExact

/-- Converting appended associations preserves first-binding precedence. -/
@[hol "HOL/src/finite_maps/alistScript.sml" "alist_to_fmap_APPEND"
  (fmap_as_finite_support_result_observations :=
    [Flapjack.HolFiniteMapExact.alistToFmap, Flapjack.HolFiniteMapExact.union])]
theorem alistToFmap_append {K V : Type} (left right : List (K × V)) :
    alistToFmap (left ++ right) = union (alistToFmap left) (alistToFmap right) := by
  classical
  induction left with
  | nil =>
    apply HolFiniteMapExact.ext_lookup
    intro key
    rfl
  | cons entry rest ih =>
    apply HolFiniteMapExact.ext_lookup
    intro key
    simp only [List.cons_append]
    by_cases same : key = entry.1
    · subst key
      rw [HolFiniteMapExact.lookup_alistToFmap_head, HolFiniteMapExact.lookup_union,
        HolFiniteMapExact.lookup_alistToFmap_head]
    · rw [HolFiniteMapExact.lookup_alistToFmap_tail entry (rest ++ right) key same,
        HolFiniteMapExact.lookup_union, HolFiniteMapExact.lookup_alistToFmap_tail entry rest key same,
        ih, HolFiniteMapExact.lookup_union]

end Flapjack.HolFiniteMapExact
