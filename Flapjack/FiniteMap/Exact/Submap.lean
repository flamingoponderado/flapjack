module

public import Flapjack.FiniteMap.SubmapExact
public import Flapjack.FiniteMap.MapKeys
public import Flapjack.FiniteMap.DomainExact
public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

/-! HOL finite-map submap and domain correspondence. -/
namespace Flapjack.HolFiniteMapExact

/-- Canonical finite-map parameter roundtrips for the source domain theorem. -/
theorem holFmapAsFiniteSupportParamWitness_submapFdomSubset_f1 {α β : Type}
    (f1 : HolFiniteMapExact α β) (key : α) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f1)).lookup key = f1.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f1)).finiteSupport = f1.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f1) = f1 := by
  cases f1
  exact ⟨rfl, rfl, rfl⟩

theorem holFmapAsFiniteSupportParamWitness_submapFdomSubset_f2 {α β : Type}
    (f2 : HolFiniteMapExact α β) (key : α) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f2)).lookup key = f2.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f2)).finiteSupport = f2.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f2) = f2 := by
  cases f2
  exact ⟨rfl, rfl, rfl⟩

@[hol "HOL/src/finite_maps/finite_mapScript.sml" "SUBMAP_FDOM_SUBSET"
  (fmap_as_finite_support_parameters := [f1, f2])]
theorem submapFdomSubset {α β : Type} (f1 : HolFiniteMapExact α β)
    (f2 : HolFiniteMapExact α β) (h : f1.submap f2) :
    Set.Subset f1.domain f2.domain := by
  intro key present
  change f1.lookup key ≠ none at present
  change f2.lookup key ≠ none
  cases found : f1.lookup key with
  | none => exact (present found).elim
  | some value => rw [h key value found]; simp

/-- Canonical finite-map parameter roundtrips for the source equality theorem. -/
theorem holFmapAsFiniteSupportParamWitness_eqFdomSubmap_f {α β : Type}
    (f : HolFiniteMapExact α β) (key : α) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f := by
  cases f
  exact ⟨rfl, rfl, rfl⟩

theorem holFmapAsFiniteSupportParamWitness_eqFdomSubmap_g {α β : Type}
    (g : HolFiniteMapExact α β) (key : α) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad g)).lookup key = g.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad g)).finiteSupport = g.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad g) = g := by
  cases g
  exact ⟨rfl, rfl, rfl⟩

@[hol "HOL/src/finite_maps/finite_mapScript.sml" "EQ_FDOM_SUBMAP"
  (fmap_as_finite_support_parameters := [f, g])]
theorem eqFdomSubmap {α β : Type} (f : HolFiniteMapExact α β) (g : HolFiniteMapExact α β) :
    f = g ↔ f.submap g ∧ f.domain = g.domain := by
  constructor
  · intro eq
    subst g
    exact ⟨submap_refl f, rfl⟩
  · rintro ⟨sub, domain⟩
    apply ext_lookup
    intro key
    cases found : f.lookup key with
    | some value => exact (sub key value found).symm
    | none =>
      have absent : key ∉ f.domain := by
        change ¬ f.lookup key ≠ none
        simp [found]
      rw [domain] at absent
      change ¬ g.lookup key ≠ none at absent
      exact (Classical.not_not.mp absent).symm


end Flapjack.HolFiniteMapExact
