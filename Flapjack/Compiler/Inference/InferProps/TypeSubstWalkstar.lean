module

public import Flapjack.Compiler.Inference.Infer.TypeSubst
public import Flapjack.Compiler.Inference.Unify.Walkstar

@[expose] public section

namespace Flapjack.Compiler.Inference.InferProps.TypeSubstWalkstar
open Flapjack.Compiler.Inference.Infer
open Flapjack.Compiler.Inference.Unify
open Flapjack.TypeSystemHOL Flapjack.Basis.Pure.MlString

/-- First-match lookup commutes with applying a function to each zipped
    value. This structural helper is used for HOL's paired substitution. -/
private theorem lookupZipMap (names : List MlString) (values : List Nat)
    (name : MlString) (f : Nat → InferT) :
    (names.zip (values.map f)).lookup name = ((names.zip values).lookup name).map f := by
  induction names generalizing values with
  | nil => rfl
  | cons n names ih =>
    cases values with
    | nil => rfl
    | cons v values =>
      by_cases h : name = n
      · subst name; simp
      · have hne : (name == n) = false := by simp [h]
        simpa [List.lookup, hne] using ih values

mutual
/-- Type case of HOL's mutual substitution/walkstar induction. -/
private theorem typeSwap (t : SemanticT) (names : List MlString)
    (s : HolFiniteMapExact Nat InferT) (offset : Nat) (h : tWfs s) :
    tWalkstar s (inferTypeSubst
      (names.zip ((List.range names.length).map (fun n => InferT.uvar (offset + n)))) t) =
    inferTypeSubst
      (names.zip ((List.range names.length).map (fun n => tWalkstar s (InferT.uvar (offset + n))))) t := by
  cases t with
  | var name =>
    simp only [inferTypeSubst, lookupZipMap]
    cases found : (names.zip (List.range names.length)).lookup name with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      exact (tWalkstarEqn1 s 0 [] 0 h).1
    | some index => simp
  | varDb index =>
    simpa [inferTypeSubst] using (tWalkstarEqn1 s index [] 0 h).1
  | app ts tc =>
    rw [(inferTypeSubstAlt _ (.implode []) 0 ts tc).2.2,
      (inferTypeSubstAlt _ (.implode []) 0 ts tc).2.2]
    rw [(tWalkstarEqn1 s 0 _ tc h).2]
    congr 1
    exact listSwap ts names s offset h
termination_by sizeOf t

/-- List case of the same mutual induction; this is proof infrastructure,
    not a separate HOL declaration. -/
private theorem listSwap (ts : List SemanticT) (names : List MlString)
    (s : HolFiniteMapExact Nat InferT) (offset : Nat) (h : tWfs s) :
    (ts.map (inferTypeSubst
      (names.zip ((List.range names.length).map (fun n => InferT.uvar (offset + n)))))).map (tWalkstar s) =
    ts.map (inferTypeSubst
      (names.zip ((List.range names.length).map (fun n => tWalkstar s (InferT.uvar (offset + n)))))) := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    simp only [List.map_cons]
    rw [typeSwap t names s offset h, listSwap ts names s offset h]
termination_by sizeOf ts
end

/-- The canonical-map codec applies to either independently quantified
    inference substitution. -/
theorem holFmapAsFiniteSupportNestedWalkstarWitness
    (map : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad map)).lookup key = map.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad map)).finiteSupport = map.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad map) = map :=
  holFmapAsFiniteSupportParamWitness_tVR_subst map key

/-- The type and list substitution/walkstar equations under the original
    well-formedness assumption. A qualifier for the independently quantified
    finite-map binders is needed before this HOL theorem can be tagged. -/
theorem substInferSubstSwap :
    (∀ (t : SemanticT) (names : List MlString) (s : HolFiniteMapExact Nat InferT) (offset : Nat),
      tWfs s →
      tWalkstar s (inferTypeSubst
        (names.zip ((List.range names.length).map (fun n => InferT.uvar (offset + n)))) t) =
      inferTypeSubst
        (names.zip ((List.range names.length).map (fun n => tWalkstar s (InferT.uvar (offset + n))))) t) ∧
    (∀ (ts : List SemanticT) (names : List MlString) (s : HolFiniteMapExact Nat InferT) (offset : Nat),
      tWfs s →
      (ts.map (inferTypeSubst
        (names.zip ((List.range names.length).map (fun n => InferT.uvar (offset + n)))))).map (tWalkstar s) =
      ts.map (inferTypeSubst
        (names.zip ((List.range names.length).map (fun n => tWalkstar s (InferT.uvar (offset + n))))))) := by
  exact ⟨typeSwap, listSwap⟩

end Flapjack.Compiler.Inference.InferProps.TypeSubstWalkstar
