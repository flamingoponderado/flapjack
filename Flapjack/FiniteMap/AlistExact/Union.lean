module

public import Flapjack.FiniteMap.AlistExact
public import Flapjack.FiniteMap.AlistExact.Append
public import Flapjack.FiniteMap.EmptyExact
public import Flapjack.FiniteMap.FunionFupdateExact
public import Flapjack.FiniteMap.UnionExact
public import Flapjack.FiniteMap.MapKeys

@[expose] public section

/-!
# Association-list union, reverse and update-list laws

Counterparts of `FUNION_alist_to_fmap` (`HOL/src/finite_maps/alistScript.sml`)
and `FUPDATE_LIST_alist_to_fmap` / `ALL_DISTINCT_alist_to_fmap_REVERSE`
(`cakeml/misc/miscScript.sml`) over the canonical finite-support carrier.
`alistToFmap` keeps first-binding precedence, `|++` is `updateListEq`, `⊌` is
`union` and `|+` is `updateEq`.
-/

namespace Flapjack.HolFiniteMapExact

/-- Flapjack infrastructure: an update list with no entries leaves the map. -/
theorem updateListEq_nil [DecidableEq α] (map : HolFiniteMapExact α β) :
    map.updateListEq ([] : List (α × β)) = map := by
  apply ext_lookup
  intro key
  simp [FUPDATE_LIST_HOL]

/-- Flapjack infrastructure: the `updateListEq` fold splits over appended entries. -/
theorem updateListEq_append [DecidableEq α] (map : HolFiniteMapExact α β)
    (first second : List (α × β)) :
    map.updateListEq (first ++ second) = (map.updateListEq first).updateListEq second := by
  apply ext_lookup
  intro key
  simp only [lookup_updateListEq]
  induction first generalizing map with
  | nil =>
    simp [updateListEq_nil, FUPDATE_LIST_HOL]
  | cons entry rest ih =>
    simp only [List.cons_append, FUPDATE_LIST_HOL_cons]
    exact ih (map.updateEq entry)

/-- Flapjack infrastructure: a one-entry update list is a single update. -/
theorem updateListEq_single [DecidableEq α] (map : HolFiniteMapExact α β)
    (entry : α × β) :
    map.updateListEq [entry] = map.updateEq entry := by
  apply ext_lookup
  intro key
  simp only [lookup_updateListEq, lookup_updateEq, FUPDATE_LIST_HOL_cons,
    FUPDATE_LIST_HOL_nil]

/-- Flapjack infrastructure: a left-biased union with the empty map on the left
is the right operand. -/
theorem union_empty_left (right : HolFiniteMapExact α β) : union empty right = right := by
  apply ext_lookup
  intro key
  rfl

/-- Flapjack infrastructure: a left-biased union with the empty map on the right
is the left operand. -/
theorem union_empty_right (left : HolFiniteMapExact α β) : union left empty = left := by
  apply ext_lookup
  intro key
  simp only [lookup_union]
  cases hl : left.lookup key
  · simp
  · simp

/-- Flapjack infrastructure: updating the left operand after a left-biased union
is the union of the updated left operand. -/
theorem union_updateEq_left [DecidableEq α] (left right : HolFiniteMapExact α β)
    (entry : α × β) :
    union (left.updateEq entry) right = (union left right).updateEq entry := by
  apply ext_lookup
  intro key
  simp only [lookup_union, lookup_updateEq, FUPDATE_HOL]
  by_cases same : key = entry.1
  · simp [same]
  · simp [same]

/-- Flapjack infrastructure: an empty association list is the empty map. -/
theorem alistToFmap_nil {α β : Type} [DecidableEq α] :
    alistToFmap ([] : List (α × β)) = empty := by
  apply ext_lookup
  intro key
  simp [alistToFmap, FUPDATE_LIST_HOL]

/-- Flapjack infrastructure: a one-entry association list is a single update of
the empty map. -/
theorem alistToFmap_single [DecidableEq α] (entry : α × β) :
    alistToFmap [entry] = empty.updateEq entry := by
  apply ext_lookup
  intro key
  simp [alistToFmap, FUPDATE_LIST_HOL, FUPDATE_HOL]

/-- Flapjack infrastructure: an association list converts by updating with its
first entry. -/
theorem alistToFmap_cons [DecidableEq α] (entry : α × β) (rest : List (α × β)) :
    alistToFmap (entry :: rest) = (alistToFmap rest).updateEq entry := by
  apply ext_lookup
  intro key
  simp [alistToFmap, FUPDATE_LIST_HOL, List.foldl_append, FUPDATE_HOL]

/-- Canonical-map witness for the `FUNION_alist_to_fmap` map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_union_alistToFmap_right {α β : Type}
    (right : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup right) right.finiteSupport = right := by
  cases right
  rfl

/-- Original `FUNION_alist_to_fmap`. -/
@[hol "HOL/src/finite_maps/alistScript.sml" "FUNION_alist_to_fmap"
  (fmap_as_finite_support_parameters := [right])]
theorem union_alistToFmap [DecidableEq α] (entries : List (α × β))
    (right : HolFiniteMapExact α β) :
    union (alistToFmap entries) right = right.updateListEq entries.reverse := by
  induction entries with
  | nil =>
    rw [List.reverse_nil, alistToFmap_nil, updateListEq_nil]
    exact union_empty_left right
  | cons entry rest ih =>
    rw [alistToFmap_cons, union_updateEq_left, ih, List.reverse_cons,
      updateListEq_append, updateListEq_single]

/-- Canonical-map witness for the `FUPDATE_LIST_alist_to_fmap` map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_fupdateListAlistToFmap_map {α β : Type}
    (map : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup map) map.finiteSupport = map := by
  cases map
  rfl

/-- Original `FUPDATE_LIST_alist_to_fmap`. -/
@[hol "cakeml/misc/miscScript.sml" "FUPDATE_LIST_alist_to_fmap"
  (fmap_as_finite_support_parameters := [map])]
theorem fupdateListAlistToFmap [DecidableEq α] (entries : List (α × β))
    (map : HolFiniteMapExact α β) :
    map.updateListEq entries = union (alistToFmap entries.reverse) map := by
  rw [union_alistToFmap, List.reverse_reverse]

/-- Original `ALL_DISTINCT_alist_to_fmap_REVERSE`. -/
@[hol "cakeml/misc/miscScript.sml" "ALL_DISTINCT_alist_to_fmap_REVERSE"
  (fmap_as_finite_support_result_observations :=
    [Flapjack.HolFiniteMapExact.alistToFmap])]
theorem alistToFmapReverseNodup [DecidableEq α] (entries : List (α × β))
    (nodup : (entries.map Prod.fst).Nodup) :
    Flapjack.HolFiniteMapExact.alistToFmap entries.reverse =
      Flapjack.HolFiniteMapExact.alistToFmap entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    simp only [List.map_cons, List.nodup_cons] at nodup
    obtain ⟨hk, hrest⟩ := nodup
    rw [List.reverse_cons, alistToFmap_append, alistToFmap_single, alistToFmap_cons,
      ih hrest]
    have hlookup : (alistToFmap rest).lookup k = none := by
      cases hl : (alistToFmap rest).lookup k with
      | none => rfl
      | some value =>
        have hmem : (k, value) ∈ rest := lookup_alistToFmap_mem rest k value hl
        have hfst : k ∈ rest.map Prod.fst := List.mem_map.mpr ⟨(k, value), hmem, rfl⟩
        exact absurd hfst hk
    have hnotmem : ¬ k ∈ (alistToFmap rest).domain := by
      show ¬ (alistToFmap rest).lookup k ≠ none
      rw [hlookup]
      simp
    rw [funionFupdate2, if_neg hnotmem, union_empty_right]

end Flapjack.HolFiniteMapExact
