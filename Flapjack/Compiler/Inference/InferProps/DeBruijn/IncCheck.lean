module

public import Flapjack.Compiler.Inference.Infer.DeBruijn
public import Flapjack.Compiler.Inference.Infer.EnvironmentInvariant

@[expose] public section

/-!
# De Bruijn increment checks

Counterparts of `check_t_deBruijn_inc2` and `check_t_deBruijn_inc` from
`cakeml/compiler/inference/inferPropsScript.sml`. HOL's `infer_deBruijn_inc`
is the tagged `inferDeBruijnInc`; `UNIV` is the predicate `fun _ => True`.
-/

namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer

mutual
/-- Structural induction helper for the original increment check. -/
private theorem checkIncType (inc : Nat) (t : InferT) (tvs : Nat) (uvs : Nat → Prop)
    (h : checkT tvs uvs t) : checkT (inc + tvs) uvs (inferDeBruijnInc inc t) := by
  cases t with
  | varDb m =>
    simp only [checkT_varDb] at h
    simp only [inferDeBruijnInc, checkT_varDb]
    omega
  | uvar m => simpa [inferDeBruijnInc] using h
  | app ts tc =>
    have ht := (checkT_app tvs tc uvs ts).mp h
    simpa [inferDeBruijnInc] using checkIncList inc ts tvs uvs ht
termination_by sizeOf t

/-- List recursion for the increment check. -/
private theorem checkIncList (inc : Nat) (ts : List InferT) (tvs : Nat) (uvs : Nat → Prop)
    (h : checkTList tvs uvs ts) : checkTList (inc + tvs) uvs (inferDeBruijnIncList inc ts) := by
  cases ts with
  | nil => simp [inferDeBruijnIncList]
  | cons t ts =>
    have ht := (checkTList_cons tvs uvs t ts).mp h
    simp [inferDeBruijnIncList, checkIncType inc t tvs uvs ht.1,
      checkIncList inc ts tvs uvs ht.2]
termination_by sizeOf ts
end

/-- Original `check_t_deBruijn_inc2`: incrementing de Bruijn indices raises the
checked bound by the same amount. HOL's free `tvs` is bound explicitly. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_t_deBruijn_inc2"]
theorem checkTInferDeBruijnInc (inc : Nat) (tvs : Nat) :
    ∀ (t : InferT) (uvs : Nat → Prop), checkT tvs uvs t →
      checkT (inc + tvs) uvs (inferDeBruijnInc inc t) :=
  fun t uvs h => checkIncType inc t tvs uvs h

mutual
/-- Structural induction helper for the original bounded identity. -/
private theorem incIdentityType (inc : Nat) (t : InferT) (h : checkT 0 (fun _ => True) t) :
    inferDeBruijnInc inc t = t := by
  cases t with
  | varDb m =>
    simp only [checkT_varDb] at h
    omega
  | uvar m => simp [inferDeBruijnInc]
  | app ts tc =>
    have ht := (checkT_app 0 tc (fun _ => True) ts).mp h
    simp [inferDeBruijnInc, incIdentityList inc ts ht]
termination_by sizeOf t

/-- List recursion for the bounded identity. -/
private theorem incIdentityList (inc : Nat) (ts : List InferT)
    (h : checkTList 0 (fun _ => True) ts) : inferDeBruijnIncList inc ts = ts := by
  cases ts with
  | nil => simp [inferDeBruijnIncList]
  | cons t ts =>
    have ht := (checkTList_cons 0 (fun _ => True) t ts).mp h
    simp [inferDeBruijnIncList, incIdentityType inc t ht.1, incIdentityList inc ts ht.2]
termination_by sizeOf ts
end

/-- Original `check_t_deBruijn_inc`: a type with no free de Bruijn variables is
unchanged by any increment. HOL's `UNIV` is `fun _ => True`. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_t_deBruijn_inc"]
theorem inferDeBruijnInc_of_checkT_zero (inc : Nat) (t : InferT)
    (h : checkT 0 (fun _ => True) t) : inferDeBruijnInc inc t = t :=
  incIdentityType inc t h

end Flapjack.Compiler.Inference.InferProps
