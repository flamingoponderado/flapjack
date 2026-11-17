module

public import Flapjack.Compiler.Inference.Infer.Generalise
public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

namespace Flapjack.Compiler.Inference.InferProps.Generalise
open Flapjack.Compiler.Inference.Infer.Generalise

/-- The input substitution roundtrips through the finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_generaliseListLength_subst
    (subst : HolFiniteMapExact Nat Nat) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst := by
  cases subst
  exact ⟨rfl, rfl, rfl⟩

/-- The result substitution roundtrips through the same finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_generaliseListLength_out
    (out : HolFiniteMapExact Nat Nat) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad out)).lookup key = out.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad out)).finiteSupport = out.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad out) = out := by
  cases out
  exact ⟨rfl, rfl, rfl⟩

/-- The source-shaped finite-map generalizer preserves list length. The HOL
    theorem's input and output map binders and observed tuple result still
    require a combined representation qualifier for this statement. -/
theorem generaliseListLength (minimum next : Nat) (subst : HolFiniteMapExact Nat Nat)
    (input : List InferT) (count : Nat) (out : HolFiniteMapExact Nat Nat)
    (result : List InferT)
    (h : generaliseListMap minimum next subst input = (count, out, result)) :
    result.length = input.length := by
  induction input generalizing next subst count out result with
  | nil =>
    simp [generaliseListMap] at h
    simp [h.2.2]
  | cons t ts ih =>
    simp only [generaliseListMap] at h
    cases first : generaliseMap minimum next subst t with
    | mk headCount headRest =>
      cases headRest with
      | mk mid headType =>
        simp only [first] at h
        cases second : generaliseListMap minimum (headCount + next) mid ts with
        | mk tailCount tailRest =>
          cases tailRest with
          | mk final tailTypes =>
            simp only [second, Prod.mk.injEq] at h
            obtain ⟨_, _, rfl⟩ := h
            simpa using ih (headCount + next) mid tailCount final tailTypes second

end Flapjack.Compiler.Inference.InferProps.Generalise
