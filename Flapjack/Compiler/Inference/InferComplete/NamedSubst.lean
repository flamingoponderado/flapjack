module

public import Flapjack.Compiler.Inference.InferProps
public import Flapjack.TypeSysProps.Abbrev

@[expose] public section

/-! Conversion commutes with well-scoped named type substitution. -/

namespace Flapjack.Compiler.Inference.InferComplete
open Flapjack Flapjack.TypeSystemHOL Flapjack.TypeSysProps Flapjack.Compiler.Inference.InferProps Flapjack.Basis.Pure.MlString

private theorem lookupMap (entries : List (MlString × SemanticT)) (key : MlString) :
    (entries.map (fun p => (p.1, unconvertT p.2))).lookup key = (entries.lookup key).map unconvertT := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨name, value⟩
    by_cases same : key = name
    · subst key; simp
    · have different : (key == name) = false := by simp [same]
      simpa [List.lookup, different] using ih

mutual
private theorem convSubst (t : SemanticT) (subst : List (MlString × SemanticT)) (fvs : List MlString)
    (free : checkFreevars 0 fvs t = true) (included : ∀ n ∈ fvs, n ∈ subst.map Prod.fst) :
    unconvertT (typeSubst (HolFiniteMapExact.alistToFmap subst) t) =
      Infer.inferTypeSubst (subst.map (fun p => (p.1, unconvertT p.2))) t := by
  cases t with
  | var name =>
    have mem : name ∈ fvs := by simpa [checkFreevars] using free
    have inKeys := included name mem
    obtain ⟨entry, entryMem, entryEq⟩ := List.mem_map.mp inKeys
    cases found : subst.lookup name with
    | none =>
      have absent := List.lookup_eq_none_iff.mp found entry entryMem
      simp [entryEq] at absent
    | some value =>
      simp [typeSubst, Infer.inferTypeSubst, alistToFmapEqTypeSubstMap,
        lookupTypeSubstMap, lookupMap, found]
  | varDb n => simp [typeSubst, unconvertT, Infer.inferTypeSubst]
  | app ts id =>
    have all : checkFreevarsList 0 fvs ts = true := by simpa [checkFreevars] using free
    simp [typeSubst, unconvertT, Infer.inferTypeSubst, convSubstList ts subst fvs all included]
termination_by sizeOf t

private theorem convSubstList (ts : List SemanticT) (subst : List (MlString × SemanticT))
    (fvs : List MlString) (free : checkFreevarsList 0 fvs ts = true)
    (included : ∀ n ∈ fvs, n ∈ subst.map Prod.fst) :
    unconvertTList (typeSubstList (HolFiniteMapExact.alistToFmap subst) ts) =
      Infer.inferTypeSubstList (subst.map (fun p => (p.1, unconvertT p.2))) ts := by
  cases ts with
  | nil => simp [typeSubstList, unconvertTList, Infer.inferTypeSubstList]
  | cons t ts =>
    simp only [checkFreevarsList, Bool.and_eq_true] at free
    simp [typeSubstList, unconvertTList, Infer.inferTypeSubstList,
      convSubst t subst fvs free.1 included, convSubstList ts subst fvs free.2 included]
termination_by sizeOf ts
end

/-- Named semantic substitution commutes with inference-type conversion. -/
@[hol "cakeml/compiler/inference/proofs/inferCompleteScript.sml" "unconvert_type_subst"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.alistToFmap])]
theorem unconvertTypeSubst :
    (∀ t subst fvs, checkFreevars 0 fvs t = true ∧ (∀ n ∈ fvs, n ∈ subst.map Prod.fst) →
      unconvertT (typeSubst (HolFiniteMapExact.alistToFmap subst) t) =
        Infer.inferTypeSubst (subst.map (fun p => (p.1, unconvertT p.2))) t) ∧
    (∀ (ts : List SemanticT) (subst : List (MlString × SemanticT)) fvs, ts.all (checkFreevars 0 fvs) = true ∧ (∀ n ∈ fvs, n ∈ subst.map Prod.fst) →
      ts.map (fun t => unconvertT (typeSubst (HolFiniteMapExact.alistToFmap subst) t)) =
        ts.map (Infer.inferTypeSubst (subst.map (fun p => (p.1, unconvertT p.2))))) := by
  constructor
  · intro t subst fvs h
    exact convSubst t subst fvs h.1 h.2
  · intro ts subst fvs h
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      simp [convSubst t subst fvs h.1.1 h.2, ih ⟨h.1.2, h.2⟩]
end Flapjack.Compiler.Inference.InferComplete
