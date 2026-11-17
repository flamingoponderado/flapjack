module

public import Flapjack.HOL.Unification.Subst
public import Flapjack.FiniteMap.DomainExact

@[expose] public section

/-! Variable walking for well-formed first-order substitutions. -/
namespace Flapjack.HOL.Unification

/-- Recursion body used to construct the walker from well-foundedness. -/
def vwalkBody {α : Type} (subst : HolFiniteMapExact Nat (Term α))
    (v : Nat) (rec : ∀ u, vR subst u v → Term α) : Term α :=
  match h : subst.lookup v with
  | none => .var v
  | some (.var u) => rec u (by simp [vR, h, vars])
  | some (.pair left right) => .pair left right
  | some (.const c) => .const c

/-- The walker follows variable bindings using well-founded recursion. Outside
    `wfs`, HOL's defining equation does not constrain the result; this implementation picks
    `Var v` there, and no unconditional correspondence is claimed. -/
noncomputable def vwalk {α : Type} (subst : HolFiniteMapExact Nat (Term α))
    (v : Nat) : Term α := by
  classical
  exact if h : wfs subst then h.fix (vwalkBody subst) v else .var v

/-- The canonical substitution map survives the broad-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_vwalkEq_subst {α : Type}
    (subst : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst :=
  holFmapAsFiniteSupportParamWitness_vR_subst subst key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkScript.sml" "vwalk_def"
  (fmap_as_finite_support_parameters := [subst])]
theorem vwalkEq {α : Type} (subst : HolFiniteMapExact Nat (Term α))
    (h : wfs subst) : ∀ v : Nat,
    vwalk subst v = match subst.lookup v with
      | some (.var u) => vwalk subst u
      | some t => t
      | none => .var v := by
  intro v
  classical
  simp only [vwalk, dif_pos h]
  rw [WellFounded.fix_eq h (vwalkBody subst) v]
  unfold vwalkBody
  split <;> simp_all

/-- The canonical substitution map survives the broad-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_notFdomVwalk_subst {α : Type}
    (subst : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst :=
  holFmapAsFiniteSupportParamWitness_vR_subst subst key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkScript.sml" "NOT_FDOM_vwalk"
  (fmap_as_finite_support_parameters := [subst])]
theorem notFdomVwalk {α : Type} (subst : HolFiniteMapExact Nat (Term α))
    (v : Nat) (h : wfs subst ∧ v ∉ subst.domain) : vwalk subst v = .var v := by
  have missing : subst.lookup v = none := by
    have absent := h.2
    change ¬ (subst.lookup v ≠ none) at absent
    exact Classical.not_not.mp absent
  rw [vwalkEq subst h.1 v, missing]

end Flapjack.HOL.Unification
