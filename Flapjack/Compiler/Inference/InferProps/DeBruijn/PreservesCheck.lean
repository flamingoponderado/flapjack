module

public import Flapjack.Compiler.Inference.Infer.DeBruijn
public import Flapjack.Compiler.Inference.Infer.EnvironmentInvariant

@[expose] public section

namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer

mutual
/-- Structural induction helper for the original substitution check. -/
private theorem checkSubstType (s : List InferT) (n : Nat) (uvs : Nat → Prop)
    (hs : ∀ t ∈ s, checkT n uvs t) (t : InferT)
    (ht : checkT (n + s.length) uvs t) : checkT n uvs (inferDeBruijnSubst s t) := by
  cases t with
  | varDb k =>
    have hk : k < n + s.length := by simpa using ht
    by_cases h : k < s.length
    · have hm : s[k] ∈ s := List.getElem_mem h
      simpa [inferDeBruijnSubst, h] using hs s[k] hm
    · have hk' : k - s.length < n := by omega
      simpa [inferDeBruijnSubst, h] using hk'
  | uvar k => simpa [inferDeBruijnSubst] using ht
  | app ts tc =>
    have ht' := (checkT_app (n + s.length) tc uvs ts).mp ht
    have hc := checkSubstList s n uvs hs ts ht'
    simpa [inferDeBruijnSubst] using hc
termination_by sizeOf t

/-- List recursion used by the structural induction on inference types. -/
private theorem checkSubstList (s : List InferT) (n : Nat) (uvs : Nat → Prop)
    (hs : ∀ t ∈ s, checkT n uvs t) (ts : List InferT)
    (ht : checkTList (n + s.length) uvs ts) :
    checkTList n uvs (inferDeBruijnSubstList s ts) := by
  cases ts with
  | nil => simp [inferDeBruijnSubstList]
  | cons t ts =>
    have ht' := (checkTList_cons (n + s.length) uvs t ts).mp ht
    simp [inferDeBruijnSubstList, checkSubstType s n uvs hs t ht'.1,
      checkSubstList s n uvs hs ts ht'.2]
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_t_infer_deBruijn_subst"]
theorem checkTInferDeBruijnSubst (subst : List InferT) (t : InferT)
    (tvs : Nat) (uvs : Nat → Prop)
    (h : checkT (tvs + subst.length) uvs t ∧ (∀ x ∈ subst, checkT tvs uvs x)) :
    checkT tvs uvs (inferDeBruijnSubst subst t) :=
  checkSubstType subst tvs uvs h.2 t h.1

mutual
/-- Structural induction helper for the original reverse substitution check. -/
private theorem uncheckSubstType (s : List InferT) (n : Nat) (uvs : Nat → Prop)
    (t : InferT) (ht : checkT n uvs (inferDeBruijnSubst s t)) :
    checkT (n + s.length) uvs t := by
  cases t with
  | varDb k =>
    by_cases hk : k < s.length
    · have hh : k < n + s.length := by omega
      simpa using hh
    · have h' : k - s.length < n := by simpa [inferDeBruijnSubst, hk] using ht
      have hh : k < n + s.length := by omega
      simpa using hh
  | uvar k => simpa [inferDeBruijnSubst] using ht
  | app ts tc =>
    have ht' : checkTList n uvs (inferDeBruijnSubstList s ts) := by
      simpa [inferDeBruijnSubst] using ht
    exact (checkT_app (n + s.length) tc uvs ts).mpr (uncheckSubstList s n uvs ts ht')
termination_by sizeOf t

/-- List recursion used by the reverse structural induction. -/
private theorem uncheckSubstList (s : List InferT) (n : Nat) (uvs : Nat → Prop)
    (ts : List InferT) (ht : checkTList n uvs (inferDeBruijnSubstList s ts)) :
    checkTList (n + s.length) uvs ts := by
  cases ts with
  | nil => simp
  | cons t ts =>
    have ht' : checkT n uvs (inferDeBruijnSubst s t) ∧
        checkTList n uvs (inferDeBruijnSubstList s ts) := by
      simpa [inferDeBruijnSubstList] using ht
    exact (checkTList_cons (n + s.length) uvs t ts).mpr
      ⟨uncheckSubstType s n uvs t ht'.1, uncheckSubstList s n uvs ts ht'.2⟩
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "infer_deBruijn_subst_uncheck"]
theorem inferDeBruijnSubstUncheck (s : List InferT) (t : InferT)
    (maxTvs : Nat) (uvs : Nat → Prop)
    (h : checkT maxTvs uvs (inferDeBruijnSubst s t)) :
    checkT (maxTvs + s.length) uvs t :=
  uncheckSubstType s maxTvs uvs t h

end Flapjack.Compiler.Inference.InferProps
