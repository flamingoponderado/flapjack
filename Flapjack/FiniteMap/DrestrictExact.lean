module

public import Flapjack.FiniteMap.DomainExact
public import Flapjack.FiniteMap.EmptyExact
public import Flapjack.FiniteMap.Exact
public import Flapjack.Misc.FiniteMapApply
public import Flapjack.Pancake.Semantics.PanCommonProps.FiniteMapExact

@[expose] public section

/-!
# `DRESTRICT` and `FEVERY` over the canonical finite-support carrier

Counterparts of `DRESTRICT_DEF`, `FLOOKUP_DRESTRICT`, `FEVERY_DEF` and
`FEVERY_ALL_FLOOKUP` from `HOL/src/finite_maps/finite_mapScript.sml`, and of
`fevery_to_drestrict` from `cakeml/misc/miscScript.sml`.
-/

namespace Flapjack.HolFiniteMapExact

/-- Independent raw lookup for the `DRESTRICT` codec witness: keep the binding
only when the key is both defined and in the restricting set. -/
noncomputable def drestrictRaw (lookup : α → Option β) (r : Set α) (key : α) : Option β := by
  classical
  exact if lookup key ≠ none ∧ key ∈ r then lookup key else none

open Classical in
/-- The constant introduced by HOL's `DRESTRICT_DEF` specification: the map
restricted to the set `r`, keeping exactly the bindings whose keys lie in
`FDOM f INTER r`. -/
@[hol "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_DEF"
  (fmap_as_finite_support_result)]
noncomputable def drestrict (map : HolFiniteMapExact α β) (r : Set α) :
    HolFiniteMapExact α β where
  lookup key := drestrictRaw map.lookup r key
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := map.finiteSupport
    refine ⟨keys, ?_⟩
    intro key hlookup
    by_cases h : map.lookup key ≠ none ∧ key ∈ r
    · have hne : map.lookup key ≠ none := by
        unfold drestrictRaw at hlookup
        rwa [if_pos h] at hlookup
      exact hkeys key hne
    · unfold drestrictRaw at hlookup
      rw [if_neg h] at hlookup
      exact absurd hlookup (by simp)

/-- The canonical `DRESTRICT` agrees with the independent raw restriction. -/
theorem holFmapAsFiniteSupportResultWitness_drestrict {α β : Type}
    (map : HolFiniteMapExact α β) (r : Set α) (key : α) :
    (drestrict map r).lookup key = drestrictRaw map.lookup r key := rfl

/-- Canonical-map witness for the `DRESTRICT_DEF` specification's map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_drestrict_spec_map {α β : Type}
    (map : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup map) map.finiteSupport = map := by
  cases map
  rfl

open Classical in
/-- The theorem returned by HOL's `DRESTRICT_DEF` specification. -/
@[hol "HOL/src/finite_maps/finite_mapScript.sml" "DRESTRICT_DEF"
  (fmap_as_finite_support_parameters := [map])
  (total_function_inhabitants := [β])]
theorem drestrict_spec {α β : Type} [Nonempty β] (map : HolFiniteMapExact α β)
    (r : Set α) :
    (drestrict map r).domain = map.domain ∩ r ∧
      ∀ x, holFapply (drestrict map r) x =
        if x ∈ map.domain ∩ r then holFapply map x else holFapply empty x := by
  constructor
  · ext x
    show (drestrict map r).lookup x ≠ none ↔ x ∈ map.domain ∩ r
    have hmem : (x ∈ map.domain ∩ r) ↔ (map.lookup x ≠ none ∧ x ∈ r) := Iff.rfl
    rw [hmem]
    simp only [drestrict, drestrictRaw]
    by_cases h : map.lookup x ≠ none ∧ x ∈ r
    · rw [if_pos h]
      exact ⟨fun _ => h, fun _ => h.1⟩
    · rw [if_neg h]
      constructor
      · intro hne
        exact absurd rfl hne
      · intro hh
        exact absurd hh h
  · intro x
    by_cases h : x ∈ map.domain ∩ r
    · rw [if_pos h]
      have hpair : map.lookup x ≠ none ∧ x ∈ r := h
      have hlookup : (drestrict map r).lookup x = map.lookup x := by
        simp only [drestrict, drestrictRaw, if_pos hpair]
      simp [holFapply, hlookup]
    · rw [if_neg h]
      have hpair : ¬ (map.lookup x ≠ none ∧ x ∈ r) := h
      have hlookup : (drestrict map r).lookup x = none := by
        simp only [drestrict, drestrictRaw, if_neg hpair]
      simp [holFapply, hlookup]

/-- Canonical-map witness for the `FLOOKUP_DRESTRICT` map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_flookupDrestrict_fm {α β : Type}
    (fm : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup fm) fm.finiteSupport = fm := by
  cases fm
  rfl

open Classical in
/-- Original `FLOOKUP_DRESTRICT`. -/
@[hol "HOL/src/finite_maps/finite_mapScript.sml" "FLOOKUP_DRESTRICT"
  (fmap_as_finite_support_parameters := [fm])]
theorem flookupDrestrict {α β : Type} (fm : HolFiniteMapExact α β) (s : Set α) (k : α) :
    (drestrict fm s).lookup k = if k ∈ s then fm.lookup k else none := by
  by_cases h : k ∈ s
  · rw [if_pos h]
    by_cases hk : k ∈ fm.domain
    · have hpair : fm.lookup k ≠ none ∧ k ∈ s := ⟨hk, h⟩
      simp only [drestrict, drestrictRaw, if_pos hpair]
    · have hpair : ¬ (fm.lookup k ≠ none ∧ k ∈ s) := fun hp => hk hp.1
      have hnone : fm.lookup k = none := by
        cases hl : fm.lookup k
        · rfl
        · have hmem : k ∈ fm.domain := by
            show fm.lookup k ≠ none
            rw [hl]
            simp
          exact absurd hmem hk
      simp only [drestrict, drestrictRaw, if_neg hpair]
      exact hnone.symm
  · rw [if_neg h]
    have hpair : ¬ (fm.lookup k ≠ none ∧ k ∈ s) := fun hp => h hp.2
    simp only [drestrict, drestrictRaw, if_neg hpair]

/-- Canonical-map witness for the `FEVERY_DEF` map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_fevery_f {α β : Type}
    (f : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup f) f.finiteSupport = f := by
  cases f
  rfl

/-- HOL `FEVERY`: the predicate holds for every binding of the map. -/
@[hol "HOL/src/finite_maps/finite_mapScript.sml" "FEVERY_DEF"
  (fmap_as_finite_support_parameters := [f])
  (total_function_inhabitants := [β])]
noncomputable def fevery {α β : Type} [Nonempty β] (P : α × β → Prop)
    (f : HolFiniteMapExact α β) : Prop :=
  ∀ x, x ∈ f.domain → P (x, holFapply f x)

/-- Canonical-map witness for the `FEVERY_ALL_FLOOKUP` map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_feveryAllFlookup_f {α β : Type}
    (f : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup f) f.finiteSupport = f := by
  cases f
  rfl

/-- Original `FEVERY_ALL_FLOOKUP`. -/
@[hol "HOL/src/finite_maps/finite_mapScript.sml" "FEVERY_ALL_FLOOKUP"
  (fmap_as_finite_support_parameters := [f])
  (total_function_inhabitants := [β])]
theorem feveryAllFlookup {α β : Type} [Nonempty β] (P : α × β → Prop)
    (f : HolFiniteMapExact α β) :
    (∀ x, x ∈ f.domain → P (x, holFapply f x)) ↔
      ∀ k v, f.lookup k = some v → P (k, v) := by
  constructor
  · intro h k v hv
    have hmem : k ∈ f.domain := by
      show f.lookup k ≠ none
      rw [hv]
      simp
    have hk : P (k, holFapply f k) := h k hmem
    rwa [holFapply_of_lookup hv] at hk
  · intro h k hmem
    cases hl : f.lookup k with
    | none => exact absurd hl hmem
    | some v =>
      have hv : holFapply f k = v := holFapply_of_lookup hl
      rw [hv]
      exact h k v hl

/-- Canonical-map witness for the `fevery_to_drestrict` map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_feveryToDrestrict_m {α β : Type}
    (m : HolFiniteMapExact α β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup m) m.finiteSupport = m := by
  cases m
  rfl

open Classical in
/-- Original `fevery_to_drestrict`. -/
@[hol "cakeml/misc/miscScript.sml" "fevery_to_drestrict"
  (fmap_as_finite_support_parameters := [m])
  (total_function_inhabitants := [β])]
theorem feveryToDrestrict {α β : Type} [Nonempty β] (P : α × β → Prop)
    (m : HolFiniteMapExact α β) (s : Set α) :
    (∀ x, x ∈ m.domain → P (x, holFapply m x)) →
      ∀ x, x ∈ (drestrict m s).domain → P (x, holFapply (drestrict m s) x) := by
  intro h x hx
  have hxpair : x ∈ m.domain ∩ s := by
    rw [← (drestrict_spec m s).1]
    exact hx
  have happly : holFapply (drestrict m s) x = holFapply m x := by
    rw [(drestrict_spec m s).2 x, if_pos hxpair]
  rw [happly]
  exact h x hxpair.1

end Flapjack.HolFiniteMapExact
