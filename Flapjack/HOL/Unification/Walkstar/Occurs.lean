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
      have same : walkstar s (.var u) = walkstar s t' := by
        classical
        simp only [walkstar, dif_pos hw]
        simpa [eq] using normalizeWalkVar s hw u
      rw [same]
      exact ih
  · have allTerms : ∀ t, vars (walkstar s t) v → Oc s t v := by
      apply walkstarInd s hw
      intro t ih hv
      have we := walkstarEq s hw t
      have onwalk : Oc s (walk s t) v := by
        cases hit : walk s t with
        | var u =>
          have eqv : v = u := by
            rw [we, hit] at hv
            exact hv
          subst v
          have absent : u ∉ s.domain := by
            cases t with
            | var x => exact vwalkToVar s hw x u hit
            | pair a b => simp [walk] at hit
            | const c => simp [walk] at hit
          exact .direct rfl absent
        | const c =>
          have : False := by
            rw [we, hit] at hv
            exact hv
          exact this.elim
        | pair a b =>
          have hvars : vars (walkstar s a) v ∨ vars (walkstar s b) v := by
            rw [we, hit] at hv
            exact hv
          rcases hvars with ha | hb
          · have oa := ih.2 a b hit ha
            exact ocSub s a (.pair a b) v (fun _ h => Or.inl h) oa
          · have ob := ih.1 a b hit hb
            exact ocSub s b (.pair a b) v (fun _ h => Or.inr h) ob
      cases t with
      | var u =>
        apply Oc.follow (t := .var u) (u := u) rfl rfl
        exact onwalk
      | pair a b => exact onwalk
      | const c => exact onwalk
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
