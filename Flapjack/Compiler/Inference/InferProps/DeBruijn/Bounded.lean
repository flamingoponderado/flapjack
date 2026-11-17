module

public import Flapjack.Compiler.Inference.Infer.DeBruijn
public import Flapjack.Compiler.Inference.Infer.EnvironmentInvariant

@[expose] public section

namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer

mutual
/-- Structural induction helper for the original bounded identity theorem. -/
private theorem substBoundedType (n : Nat) (t : InferT) (h : checkT n (fun _ => False) t) :
    inferDeBruijnSubst ((List.range n).map InferT.varDb) t = t := by
  cases t with
  | varDb k =>
    have hk : k < n := by simpa using h
    simp [inferDeBruijnSubst, hk]
  | uvar k => simp at h
  | app ts tc =>
    have hs : checkTList n (fun _ => False) ts := (checkT_app n tc _ ts).mp h
    simp [inferDeBruijnSubst, substBoundedList n ts hs]
termination_by sizeOf t

/-- List recursion used by the structural induction on inference types. -/
private theorem substBoundedList (n : Nat) (ts : List InferT)
    (h : checkTList n (fun _ => False) ts) :
    inferDeBruijnSubstList ((List.range n).map InferT.varDb) ts = ts := by
  cases ts with
  | nil => simp [inferDeBruijnSubstList]
  | cons t ts =>
    have hs := (checkTList_cons n _ t ts).mp h
    simp [inferDeBruijnSubstList, substBoundedType n t hs.1, substBoundedList n ts hs.2]
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "infer_deBruijn_subst_id2"]
theorem inferDeBruijnSubstId2 (n : Nat) :
    (∀ t, checkT n (fun _ => False) t →
      inferDeBruijnSubst ((List.range n).map InferT.varDb) t = t) ∧
    (∀ ts : List InferT, (∀ t ∈ ts, checkT n (fun _ => False) t) →
      ts.map (inferDeBruijnSubst ((List.range n).map InferT.varDb)) = ts) := by
  constructor
  · exact substBoundedType n
  · intro ts h
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp [substBoundedType n t h.1, ih h.2]

end Flapjack.Compiler.Inference.InferProps
