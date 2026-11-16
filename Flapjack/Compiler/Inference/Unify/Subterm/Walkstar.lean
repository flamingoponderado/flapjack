module

public import Flapjack.Compiler.Inference.Unify.Subterm
public import Flapjack.Compiler.Inference.Unify.WorklistRelation
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Structural subterms decrease in HOL's walkstar ordering. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

private theorem subtermStepWalkstarR {α β : Type} (s : HolFiniteMapExact Nat (Term β))
    (t u : Term α) (h : (∃ v, u = .pair t v) ∨ ∃ v, u = .pair v t) :
    walkstarR s t u := by
  classical
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · by_cases hv : varb v = emptyBag
    · right
      refine ⟨?_, ?_⟩
      · simp only [varb, hv, bagUnion_empty_right]
      · simp [pairCount]; omega
    · left
      simpa only [varb] using
        (tcMlt1Union2I (Relation.TransGen (vR s)) (varb v) (varb t)
          ⟨finiteVarb v, finiteVarb t, hv⟩)
  · by_cases hv : varb v = emptyBag
    · right
      refine ⟨?_, ?_⟩
      · simp only [varb, hv, bagUnion_empty_left]
      · simp [pairCount]; omega
    · left
      simpa only [varb] using
        (tcMlt1Union1I (Relation.TransGen (vR s)) (varb t) (varb v)
          ⟨finiteVarb t, finiteVarb v, hv⟩)

/-- The substitution uses the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_subtermWalkstarR_s {β : Type}
    (s : HolFiniteMapExact Nat (Term β)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "cakeml/compiler/inference/unifyScript.sml" "subterm_walkstarR"
  (fmap_as_finite_support_parameters := [s])]
theorem subtermWalkstarR {α β : Type} (s : HolFiniteMapExact Nat (Term β))
    (t u : Term α) (h : subterm t u) : walkstarR s t u := by
  induction h with
  | single edge => exact subtermStepWalkstarR s _ _ edge
  | tail _ edge ih => exact walkstarRTrans s _ _ _ ⟨ih, subtermStepWalkstarR s _ _ edge⟩

end Flapjack.Compiler.Inference.Unify
