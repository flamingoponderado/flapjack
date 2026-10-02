import Flapjack.FiniteMap.UnionExact
import Mathlib.Data.Set.Finite.Basic

namespace Flapjack.HolFiniteMapExact
/-- Defined lookup domain of the canonical carrier. Flapjack infrastructure;
HOL uses FDOM on its abstract finite-map carrier. -/
def domain (map : HolFiniteMapExact α β) : Set α := {key | map.lookup key ≠ none}

/-- Finite support implies finiteness of the actual domain, independently of
which support list witnesses the carrier proposition. -/
theorem domain_finite (map : HolFiniteMapExact α β) : map.domain.Finite := by
  obtain ⟨keys, hkeys⟩ := map.finiteSupport
  exact keys.finite_toSet.subset (fun key h => hkeys key h)

/-- Cardinality of the actual defined domain, rather than the possibly
redundant support witness. Flapjack carrier infrastructure for HOL FCARD. -/
noncomputable def card (map : HolFiniteMapExact α β) : Nat :=
  map.domain_finite.toFinset.card

@[simp] theorem domain_empty : (empty : HolFiniteMapExact α β).domain = ∅ := by
  ext key
  simp [domain]

theorem domain_union (left right : HolFiniteMapExact α β) :
    (left.union right).domain = left.domain ∪ right.domain := by
  ext key
  exact union_defined_iff left right key

@[simp] theorem card_empty : (empty : HolFiniteMapExact α β).card = 0 := by
  classical
  unfold card
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro key h
  have hd := (empty : HolFiniteMapExact α β).domain_finite.mem_toFinset.mp h
  simp [domain] at hd

theorem domain_updateEq [DecidableEq α] (map : HolFiniteMapExact α β)
    (key : α) (value : β) :
    (map.updateEq (key, value)).domain = insert key map.domain := by
  ext query
  by_cases h : query = key
  · subst query; simp [domain, lookup_updateEq, FUPDATE_HOL]
  · simp [domain, lookup_updateEq, FUPDATE_HOL, h]

/-- Fresh-key update increases the actual finite domain by one. -/
theorem card_updateEq_fresh [DecidableEq α] (map : HolFiniteMapExact α β)
    (key : α) (value : β) (h : map.lookup key = none) :
    (map.updateEq (key, value)).card = map.card + 1 := by
  classical
  unfold card
  have hd := domain_updateEq map key value
  have hf : key ∉ map.domain_finite.toFinset := by
    simp [Set.Finite.mem_toFinset, domain, h]
  have he : (map.updateEq (key, value)).domain_finite.toFinset =
      insert key map.domain_finite.toFinset := by
    ext query
    simp only [Set.Finite.mem_toFinset, Finset.mem_insert]
    rw [hd]
    rfl
  rw [he, Finset.card_insert_of_notMem hf]

/-- Disjoint union counts both actual lookup domains. -/
theorem card_union_disjoint (left right : HolFiniteMapExact α β)
    (h : Disjoint left.domain right.domain) :
    (left.union right).card = left.card + right.card := by
  classical
  unfold card
  have he : (left.union right).domain_finite.toFinset =
      left.domain_finite.toFinset ∪ right.domain_finite.toFinset := by
    ext key
    simp only [Set.Finite.mem_toFinset, Finset.mem_union]
    exact union_defined_iff left right key
  rw [he, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro key hl hr
  exact Set.disjoint_left.mp h
    (left.domain_finite.mem_toFinset.mp hl) (right.domain_finite.mem_toFinset.mp hr)

/-- Existing-key update leaves the actual lookup domain unchanged. -/
theorem card_updateEq_existing [DecidableEq α] (map : HolFiniteMapExact α β)
    (key : α) (value : β) (h : map.lookup key ≠ none) :
    (map.updateEq (key, value)).card = map.card := by
  classical
  unfold card
  congr 1
  ext query
  simp only [Set.Finite.mem_toFinset]
  rw [domain_updateEq, Set.insert_eq_of_mem h]

/-- Full HOL-shaped hit-or-fresh update equation over the canonical finite
lookup domain. Source/qualifier registration remains pending. -/
theorem card_updateEq [DecidableEq α] (map : HolFiniteMapExact α β)
    (key : α) (value : β) :
    (map.updateEq (key, value)).card =
      if map.lookup key ≠ none then map.card else 1 + map.card := by
  classical
  by_cases h : map.lookup key = none
  · rw [if_neg (not_not_intro h), card_updateEq_fresh map key value h]
    omega
  · rw [if_pos h, card_updateEq_existing map key value h]

/-- Raw lookup codec for the standard canonical finite-map parameter witness;
Flapjack infrastructure, not a separate HOL declaration. -/
def toBroadlookupCardinality (map : HolFiniteMapExact α β) : α → Option β := map.lookup
def ofBroadCardinality (lookup : α → Option β)
    (finiteSupport : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact α β := ⟨lookup, finiteSupport⟩

theorem holFmapAsFiniteSupportParamWitness_fcardFupdate_map (map : HolFiniteMapExact α β) :
    ofBroadCardinality (toBroadlookupCardinality map) map.finiteSupport = map := by
  cases map
  rfl

/-- Full original FCARD_FUPDATE. HOL map equality is represented by the
classical equality decision, with no decidability or finite-key premise.
Cardinality counts the actual defined lookup domain, not support-list length. -/
@[hol "HOL/src/finite_maps/finite_mapScript.sml" "FCARD_FUPDATE"
  (fmap_as_finite_support_parameters := [map])]
theorem fcardFupdate (map : HolFiniteMapExact α β) (key : α) (value : β) :
    (@updateEq α β (Classical.typeDecidableEq α) map (key, value)).card =
      if map.lookup key ≠ none then map.card else 1 + map.card := by
  classical
  exact card_updateEq map key value
end Flapjack.HolFiniteMapExact
