module

public import Flapjack.Compiler.Inference.InferProps

@[expose] public section

/-! Type-identifier bounds for source substitutions. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.InferProps

/-- Canonical finite-map codec witness for the substitution parameter. -/
theorem holFmapAsFiniteSupportParamWitness_setTidsSubsetTypeSubst_s
    (s : HolFiniteMapExact MlString SemanticT) (key : MlString) :
    (TypeSubstBroad.ofBroad (TypeSubstBroad.toBroad s)).lookup key = s.lookup key ∧
    (TypeSubstBroad.ofBroad (TypeSubstBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    TypeSubstBroad.ofBroad (TypeSubstBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_typeSubst_subst s key

mutual
/-- Substitution preserves an identifier bound when all map values satisfy it. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "set_tids_subset_type_subst"
  (fmap_as_finite_support_parameters := [s])]
theorem setTidsSubsetTypeSubst (s : HolFiniteMapExact MlString SemanticT) (t : SemanticT) (tids : Nat → Prop) :
    (∀ key value, s.lookup key = some value → setTidsSubset tids value) ∧
      setTidsSubset tids t → setTidsSubset tids (typeSubst s t) := by
  rintro ⟨all, bound⟩ id member
  cases t with
  | var name =>
    cases found : s.lookup name with
    | none => simp [typeSubst, found, setTids] at member
    | some value => exact all name value found id (by simpa [typeSubst, found] using member)
  | varDb n => simp [typeSubst, setTids] at member
  | app ts name =>
    simp only [typeSubst, setTids] at member
    rcases member with same | nested
    · exact bound id (by simp [setTids, same])
    · apply substListBound s ts tids all ?_ id nested
      intro id h
      exact bound id (by simp [setTids, h])
termination_by sizeOf t

/-- List traversal for the source substitution bound induction. -/
private theorem substListBound (s : HolFiniteMapExact MlString SemanticT) (ts : List SemanticT)
    (tids : Nat → Prop) (all : ∀ key value, s.lookup key = some value → setTidsSubset tids value)
    (bound : ∀ id, setTidsList ts id → tids id) :
    ∀ id, setTidsList (typeSubstList s ts) id → tids id := by
  cases ts with
  | nil => simp [typeSubstList, setTidsList]
  | cons t ts =>
    intro id member
    simp only [typeSubstList, setTidsList] at member
    rcases member with head | tail
    · apply setTidsSubsetTypeSubst s t tids ⟨all, ?_⟩ id head
      intro n h
      exact bound n (by simp [setTidsList, h])
    · apply substListBound s ts tids all ?_ id tail
      intro n h
      exact bound n (by simp [setTidsList, h])
termination_by sizeOf ts
end

end Flapjack.Compiler.Inference.InferProps
