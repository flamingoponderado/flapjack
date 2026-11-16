module

public import Flapjack.HOL.Unification.Subst
public import Flapjack.HOL.Unification.Term.Finite
public import Flapjack.FiniteMap.DomainExact
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

namespace Flapjack.HOL.Unification

/-- Canonical map codec roundtrip for the range-variable operation. -/
theorem holFmapAsFiniteSupportParamWitness_rangeVars_s {α κ : Type}
    (s : HolFiniteMapExact κ (Term α)) (key : κ) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/substScript.sml" "rangevars_def"
  (fmap_as_finite_support_parameters := [s])]
def rangeVars {α κ : Type} (s : HolFiniteMapExact κ (Term α)) : Set Nat :=
  Set.sUnion (Set.image vars {t | ∃ key, s.lookup key = some t})

/-- Canonical map codec roundtrip for the range-variable finiteness theorem. -/
theorem holFmapAsFiniteSupportParamWitness_finiteRangeVars_s {α κ : Type}
    (s : HolFiniteMapExact κ (Term α)) (key : κ) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/substScript.sml" "FINITE_rangevars"
  (fmap_as_finite_support_parameters := [s])]
theorem finiteRangeVars {α κ : Type} (s : HolFiniteMapExact κ (Term α)) :
    Set.Finite (rangeVars s) := by
  classical
  obtain ⟨keys, hkeys⟩ := s.finiteSupport
  let f : κ → Term α := fun key => (s.lookup key).getD (.var 0)
  have hrange : Set.Finite {t | ∃ key, s.lookup key = some t} := by
    apply (keys.toFinset.finite_toSet.image f).subset
    rintro t ⟨key, found⟩
    refine ⟨key, ?_, ?_⟩
    · exact List.mem_toFinset.mpr (hkeys key (by simp [found]))
    · simp [f, found]
  apply Set.Finite.sUnion (hrange.image vars)
  rintro _ ⟨t, _, rfl⟩
  exact finiteVars t

/-- Canonical map codec roundtrip for the range-variable containment theorem. -/
theorem holFmapAsFiniteSupportParamWitness_inFrangeRangeVars_s {α κ : Type}
    (s : HolFiniteMapExact κ (Term α)) (key : κ) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/substScript.sml" "IN_FRANGE_rangevars"
  (fmap_as_finite_support_parameters := [s])]
theorem inFrangeRangeVars {α κ : Type} (s : HolFiniteMapExact κ (Term α)) (t : Term α)
    (h : t ∈ {t | ∃ key, s.lookup key = some t}) : Set.Subset (vars t) (rangeVars s) := by
  intro v hv
  exact Set.mem_sUnion.mpr ⟨vars t, ⟨t, h, rfl⟩, hv⟩

/-- Canonical map codec roundtrip for the substitution-variable operation. -/
theorem holFmapAsFiniteSupportParamWitness_substVars_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/substScript.sml" "substvars_def"
  (fmap_as_finite_support_parameters := [s])]
def substVars {α : Type} (s : HolFiniteMapExact Nat (Term α)) : Set Nat :=
  s.domain ∪ rangeVars s

/-- Canonical map codec roundtrip for the substitution-variable finiteness theorem. -/
theorem holFmapAsFiniteSupportParamWitness_finiteSubstVars_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/substScript.sml" "FINITE_substvars"
  (fmap_as_finite_support_parameters := [s])]
theorem finiteSubstVars {α : Type} (s : HolFiniteMapExact Nat (Term α)) :
    Set.Finite (substVars s) := by
  classical
  obtain ⟨keys, hkeys⟩ := s.finiteSupport
  have hd : s.domain.Finite := by
    apply keys.toFinset.finite_toSet.subset
    intro key present
    exact List.mem_toFinset.mpr (hkeys key present)
  exact hd.union (finiteRangeVars s)

end Flapjack.HOL.Unification
