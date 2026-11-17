module

public import Flapjack.HOL.Unification.TcallUnif
public import Flapjack.HOL.Unification.Subst.Vars
public import Flapjack.FiniteMap.MapKeys

@[expose] public section

/-! Substitution variables after an arbitrary finite-map update. -/
namespace Flapjack.HOL.Unification

/-- The canonical substitution survives the finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_substVarsFupdate_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/compilation/tcallUnifScript.sml" "substvars_FUPDATE"
  (fmap_as_finite_support_parameters := [s])]
theorem substVarsFupdate {α : Type} (s : HolFiniteMapExact Nat (Term α)) (v : Nat) (t : Term α) :
    substVars (s.updateEq (v, t)) =
      Set.union (Set.union (substVars (s.eraseEq v)) {v}) (vars t) := by
  classical
  have absent : v ∉ (s.eraseEq v).domain := by
    change ¬ (s.eraseEq v).lookup v ≠ none
    simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL]
  have update : @HolFiniteMapExact.updateEq Nat (Term α) (Classical.decEq Nat) (s.eraseEq v) (v, t) =
      s.updateEq (v, t) := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    by_cases h : key = v <;>
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, HolFiniteMapExact.eraseEq, FDOMSUB_HOL, h]
  have range := rangeVarsUpdate (s.eraseEq v) v t absent
  rw [update] at range
  have domain : (s.updateEq (v, t)).domain = Set.union (s.eraseEq v).domain {v} := by
    ext key
    by_cases h : key = v <;>
      simp [Set.union, HolFiniteMapExact.domain, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
        HolFiniteMapExact.eraseEq, FDOMSUB_HOL, h]
  rw [substVars, domain, range, substVars]
  ext x
  change (((s.eraseEq v).domain x ∨ x = v) ∨ (rangeVars (s.eraseEq v) x ∨ vars t x)) ↔
    (((s.eraseEq v).domain x ∨ rangeVars (s.eraseEq v) x) ∨ x = v) ∨ vars t x
  tauto

end Flapjack.HOL.Unification
