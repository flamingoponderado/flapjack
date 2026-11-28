module

public import Flapjack.HolRef
public import Flapjack.FiniteMap.Exact

@[expose] public section

/-!
# `NOT_MEM_FLOOKUP_ZIP`

Counterpart of `NOT_MEM_FLOOKUP_ZIP` from `cakeml/misc/miscScript.sml`: updating
a finite map with `ZIP`ped key/value lists leaves the lookup at a key that does
not occur in the key list unchanged.
-/

namespace Flapjack

/-- The first components of a `ZIP`ped list are a subset of the first list. -/
private theorem memFstZip {α β : Type} (ys : List α) (zs : List β) (n : α) :
    n ∈ (List.zip ys zs).map Prod.fst → n ∈ ys := by
  intro h
  obtain ⟨p, hp, hfst⟩ := List.mem_map.mp h
  obtain ⟨a, b⟩ := p
  have ha : a = n := hfst
  subst ha
  exact (List.of_mem_zip hp).1

/-- Original `NOT_MEM_FLOOKUP_ZIP`: a key absent from the `ZIP`ped key list is
not updated. -/
@[hol "cakeml/misc/miscScript.sml" "NOT_MEM_FLOOKUP_ZIP"]
theorem notMemFlookupZip {α β : Type} [DecidableEq α] (ys : List α)
    (xs : HolFiniteMapExact α β) (zs : List β) (n : α) (h : n ∉ ys) :
    (xs.updateListEq (List.zip ys zs)).lookup n = xs.lookup n := by
  have hmem : n ∉ (List.zip ys zs).map Prod.fst := fun hc => h (memFstZip ys zs n hc)
  exact FLOOKUP_FUPDATE_LIST_HOL_not_mem xs.lookup (List.zip ys zs) n hmem

end Flapjack
