module

public import Flapjack.Compiler.Inference.Infer.DeBruijn
public import Flapjack.Compiler.Inference.Infer.EnvironmentInvariant

@[expose] public section

/-! Composition of de Bruijn substitutions. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer

mutual
/-- Structural induction for substitution composition. -/
private theorem substTwiceType (subst1 subst2 : List InferT) (uvs : Nat → Prop)
    (t : InferT) (h : checkT subst2.length uvs t) :
    inferDeBruijnSubst subst1 (inferDeBruijnSubst subst2 t) =
      inferDeBruijnSubst (subst2.map (inferDeBruijnSubst subst1)) t := by
  cases t with
  | uvar v => simp [inferDeBruijnSubst]
  | varDb k =>
    have hk : k < subst2.length := by simpa using h
    simp [inferDeBruijnSubst, hk]
  | app ts tc =>
    have hl := (checkT_app subst2.length tc uvs ts).mp h
    simp [inferDeBruijnSubst, substTwiceList subst1 subst2 uvs ts hl]
termination_by sizeOf t

/-- List recursion for substitution composition. -/
private theorem substTwiceList (subst1 subst2 : List InferT) (uvs : Nat → Prop)
    (ts : List InferT) (h : checkTList subst2.length uvs ts) :
    inferDeBruijnSubstList subst1 (inferDeBruijnSubstList subst2 ts) =
      inferDeBruijnSubstList (subst2.map (inferDeBruijnSubst subst1)) ts := by
  cases ts with
  | nil => simp [inferDeBruijnSubstList]
  | cons t ts =>
    have hs := (checkTList_cons subst2.length uvs t ts).mp h
    simp [inferDeBruijnSubstList, substTwiceType subst1 subst2 uvs t hs.1,
      substTwiceList subst1 subst2 uvs ts hs.2]
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "infer_deBruijn_subst_twice"]
theorem inferDeBruijnSubstTwice (subst1 subst2 : List InferT) (uvs : Nat → Prop) :
    (∀ t, checkT subst2.length uvs t →
      inferDeBruijnSubst subst1 (inferDeBruijnSubst subst2 t) =
        inferDeBruijnSubst (subst2.map (inferDeBruijnSubst subst1)) t) ∧
    (∀ ts : List InferT, (∀ t ∈ ts, checkT subst2.length uvs t) →
      ts.map (inferDeBruijnSubst subst1 ∘ inferDeBruijnSubst subst2) =
        ts.map (inferDeBruijnSubst (subst2.map (inferDeBruijnSubst subst1)))) := by
  constructor
  · exact fun t h => substTwiceType subst1 subst2 uvs t h
  · intro ts h
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp [substTwiceType subst1 subst2 uvs t h.1, ih h.2]

end Flapjack.Compiler.Inference.InferProps
