module

public import Flapjack.Compiler.Inference.Infer.DeBruijn

@[expose] public section

namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer

mutual
/-- Structural induction helper for the original two-part identity theorem. -/
private theorem substEmptyType (t : InferT) : inferDeBruijnSubst [] t = t := by
  cases t with
  | varDb n => simp [inferDeBruijnSubst]
  | uvar n => simp [inferDeBruijnSubst]
  | app ts tc => simp [inferDeBruijnSubst, substEmptyList ts]
termination_by sizeOf t

/-- List recursion used by the structural induction on inference types. -/
private theorem substEmptyList (ts : List InferT) : inferDeBruijnSubstList [] ts = ts := by
  cases ts with
  | nil => simp [inferDeBruijnSubstList]
  | cons t ts => simp [inferDeBruijnSubstList, substEmptyType t, substEmptyList ts]
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "infer_deBruijn_subst_id"]
theorem inferDeBruijnSubstId : (∀ t, inferDeBruijnSubst [] t = t) ∧
    (∀ ts : List InferT, ts.map (inferDeBruijnSubst []) = ts) := by
  refine ⟨substEmptyType, ?_⟩
  intro ts
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [substEmptyType, ih]

end Flapjack.Compiler.Inference.InferProps
