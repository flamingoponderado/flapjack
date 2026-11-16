module

public import Flapjack.Compiler.Inference.Infer.EnvironmentInvariant

@[expose] public section

namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer

mutual
/-- Structural induction helper for the original type-check monotonicity result. -/
private theorem checkMonoType (t : InferT) (uvs : Nat → Prop) (tvs : Nat)
    (h : checkT tvs uvs t) (uvs' : Nat → Prop) (sub : ∀ v, uvs v → uvs' v) :
    checkT tvs uvs' t := by
  cases t with
  | varDb n => simpa using h
  | uvar n => exact (checkT_uvar tvs n uvs').mpr (sub n ((checkT_uvar tvs n uvs).mp h))
  | app ts tc =>
    exact (checkT_app tvs tc uvs' ts).mpr
      (checkMonoList ts uvs tvs ((checkT_app tvs tc uvs ts).mp h) uvs' sub)
termination_by sizeOf t

/-- List recursion used by type-check monotonicity for applications. -/
private theorem checkMonoList (ts : List InferT) (uvs : Nat → Prop) (tvs : Nat)
    (h : checkTList tvs uvs ts) (uvs' : Nat → Prop) (sub : ∀ v, uvs v → uvs' v) :
    checkTList tvs uvs' ts := by
  cases ts with
  | nil => simp
  | cons t ts =>
    have h' := (checkTList_cons tvs uvs t ts).mp h
    exact (checkTList_cons tvs uvs' t ts).mpr
      ⟨checkMonoType t uvs tvs h'.1 uvs' sub, checkMonoList ts uvs tvs h'.2 uvs' sub⟩
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_t_more5"]
theorem checkTMore5 :
    (∀ t uvs tvs, checkT tvs uvs t → ∀ uvs', (∀ v, uvs v → uvs' v) → checkT tvs uvs' t) ∧
    (∀ (ts : List InferT) uvs tvs, (∀ t ∈ ts, checkT tvs uvs t) →
      ∀ uvs', (∀ v, uvs v → uvs' v) → ∀ t ∈ ts, checkT tvs uvs' t) := by
  constructor
  · exact checkMonoType
  · intro ts uvs tvs h uvs' sub t ht
    exact checkMonoType t uvs tvs (h t ht) uvs' sub

end Flapjack.Compiler.Inference.InferProps
