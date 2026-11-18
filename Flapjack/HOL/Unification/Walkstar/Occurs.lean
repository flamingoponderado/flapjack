module

public import Flapjack.HOL.Unification.Walkstar.Induction
public import Flapjack.HOL.Unification.Walkstar.NotDomain

@[expose] public section

/-! The original inductive occurrence relation and normalization. -/
namespace Flapjack.HOL.Unification

/-- The two source occurrence rules over the first-order walker. The walker
    model is only claimed to match HOL on well-formed substitutions, so no
    unconditional correspondence is claimed for this inductive relation. -/
inductive Oc {α : Type} (s : HolFiniteMapExact Nat (Term α)) : Term α → Nat → Prop where
  | direct {t v} : vars t v → v ∉ s.domain → Oc s t v
  | follow {t v u t'} : vars t u → vwalk s u = t' → Oc s t' v → Oc s t v

/-- Occurrence is preserved when the input term gains variables. -/
private theorem ocSub {α : Type} (s : HolFiniteMapExact Nat (Term α)) (a b : Term α) (v : Nat)
    (sub : ∀ u, vars a u → vars b u) (h : Oc s a v) : Oc s b v := by
  cases h with
  | direct hv absent => exact .direct (sub _ hv) absent
  | follow hu eq h => exact .follow (sub _ hu) eq h

/-- The substitution survives the canonical finite-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_ocEqVarsWalkstar_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkstarScript.sml" "oc_eq_vars_walkstar"
  (fmap_as_finite_support_parameters := [s])]
theorem ocEqVarsWalkstar {α : Type} (s : HolFiniteMapExact Nat (Term α)) (t : Term α) (v : Nat)
    (hw : wfs s) : Oc s t v ↔ vars (walkstar s t) v := by
  constructor
  · intro h
    induction h with
    | direct hv absent => exact notFdomWalkstar s _ hw _ absent hv
    | @follow t v u t' hu eq oc ih =>
      apply walkstarVarLift s hw t u v hu
      simp only [walkstar, dif_pos hw]
      rw [normalizeWalkVar s hw u, eq]
      simpa only [walkstar, dif_pos hw] using ih
  · have allTerms : ∀ t, vars (walkstar s t) v → Oc s t v := by
      refine walkstarInd s hw (fun t => vars (walkstar s t) v → Oc s t v)
        (fun t ih hv => ?_)
      rw [walkstarEq s hw t] at hv
      have onwalk : Oc s (walk s t) v := by
        cases hit : walk s t with
        | var u =>
          rw [hit] at hv
          cases hv
          cases t with
          | var x => exact .direct rfl (vwalkToVar s hw x v hit)
          | pair a b => simp [walk] at hit
          | const c => simp [walk] at hit
        | const c =>
          rw [hit] at hv
          exact hv.elim
        | pair a b =>
          rw [hit] at hv
          rcases hv with ha | hb
          · exact ocSub s a (.pair a b) v (fun _ h => Or.inl h) (ih.2 a b hit ha)
          · exact ocSub s b (.pair a b) v (fun _ h => Or.inr h) (ih.1 a b hit hb)
      cases t <;> first | exact .follow rfl rfl onwalk | exact onwalk
    exact allTerms t

/-- The substitution survives the canonical finite-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_ocWalking_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkstarScript.sml" "oc_walking"
  (fmap_as_finite_support_parameters := [s])]
theorem ocWalking {α : Type} (s : HolFiniteMapExact Nat (Term α)) (t : Term α) (v : Nat)
    (hw : wfs s) : Oc s t v ↔ match walk s t with
      | .var u => v = u
      | .pair a b => Oc s a v ∨ Oc s b v
      | .const _ => False := by
  rw [ocEqVarsWalkstar s t v hw, walkstarEq s hw t]
  cases hit : walk s t with
  | var u => simp [vars]
  | const c => simp [vars]
  | pair a b => simp [vars, ocEqVarsWalkstar s a v hw, ocEqVarsWalkstar s b v hw]

end Flapjack.HOL.Unification
