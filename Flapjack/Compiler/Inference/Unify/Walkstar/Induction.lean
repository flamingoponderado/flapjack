module

public import Flapjack.Compiler.Inference.Unify.Walkstar
public import Flapjack.Compiler.Inference.Unify.Vars
public import Flapjack.HOL.Unification.Walk.Dependency

@[expose] public section

/-! The original induction principle for inference-type normalization. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- The induction step in the original theorem, named for the proof helpers. -/
private def walkIndStep (s : HolFiniteMapExact Nat InferT) (P : InferT → Prop) : Prop :=
  ∀ t, (∀ ts tc a, tWalk s t = .app ts tc ∧ a ∈ ts → P a) → P t

mutual
/-- Build the property for a type when it holds for its variables. -/
private theorem buildP (s : HolFiniteMapExact Nat InferT) (P : InferT → Prop)
    (step : walkIndStep s P) (t : InferT) (known : ∀ v, tVars t v → P (.uvar v)) : P t := by
  cases t with
  | uvar v =>
    apply known v
    rw [tVarsEqn.2.2 v]
    rfl
  | varDb v =>
    apply step (.varDb v)
    intro ts tc a hp
    rw [tWalkEqn.2.2 s v] at hp
    cases hp.1
  | app xs c =>
    apply step (.app xs c)
    intro ts tc a hp
    rw [tWalkEqn.2.1 s xs c] at hp
    cases hp.1
    apply buildPList s P step xs ?_ a hp.2
    intro t ht v hv
    apply known v
    rw [tVarsEqn.2.1 xs c]
    change ∃ p : Nat → Prop, (∃ t, t ∈ xs ∧ tVars t = p) ∧ p v
    exact ⟨tVars t, ⟨t, ht, rfl⟩, hv⟩
termination_by sizeOf t

/-- Structural list induction used while building the type property. -/
private theorem buildPList (s : HolFiniteMapExact Nat InferT) (P : InferT → Prop)
    (step : walkIndStep s P) (ts : List InferT)
    (known : ∀ t ∈ ts, ∀ v, tVars t v → P (.uvar v)) : ∀ a ∈ ts, P a := by
  cases ts with
  | nil => simp
  | cons t ts =>
    intro a ha
    simp only [List.mem_cons] at ha
    cases ha with
    | inl eq =>
      subst a
      exact buildP s P step t (known t (by simp))
    | inr mem =>
      apply buildPList s P step ts ?_ a mem
      intro b hb
      exact known b (by simp [hb])
termination_by sizeOf ts
end

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWalkstarInd_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_walkstar_ind"
  (fmap_as_finite_support_parameters := [s])]
theorem tWalkstarInd (s : HolFiniteMapExact Nat InferT) (hw : tWfs s) :
    ∀ P : InferT → Prop,
      (∀ t, (∀ ts tc a, tWalk s t = .app ts tc ∧ a ∈ ts → P a) → P t) → ∀ t, P t := by
  intro P step
  have allVars : ∀ v, P (.uvar v) := by
    intro v
    induction v using hw.transGen.induction with
    | h v ih =>
      apply step (.uvar v)
      intro ts tc a hp
      have walkEq : tVwalk s v = .app ts tc := by
        rw [← tWalkEqn.1 s v]
        exact hp.1
      have encodedEq : vwalk (s.map2 (fun p => encodeInferT p.2)) v =
          encodeInferT (.app ts tc) := by
        rw [encodeVwalk s hw v, walkEq]
      apply buildP s P step a
      intro u hu
      apply ih u
      apply vwalkVR (s.map2 (fun p => encodeInferT p.2)) hw v u
      constructor
      · rw [encodedEq]
        change tVars (.app ts tc) u
        rw [tVarsEqn.2.1 ts tc]
        change ∃ p : Nat → Prop, (∃ t, t ∈ ts ∧ tVars t = p) ∧ p u
        exact ⟨tVars a, ⟨a, hp.2, rfl⟩, hu⟩
      · rw [encodedEq]
        simp [encodeInferT]
  intro t
  exact buildP s P step t (fun v _ => allVars v)

end Flapjack.Compiler.Inference.Unify
