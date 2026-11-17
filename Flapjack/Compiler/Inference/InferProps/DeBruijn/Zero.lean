module

public import Flapjack.Compiler.Inference.Infer

@[expose] public section

/-! A zero de Bruijn shift is the identity on inference types. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer

mutual
private theorem shiftZeroType (t : InferT) : inferDeBruijnInc 0 t = t := by
  cases t with
  | varDb n => simp [inferDeBruijnInc]
  | uvar n => simp [inferDeBruijnInc]
  | app ts tc => simp [inferDeBruijnInc, shiftZeroList ts]
termination_by sizeOf t

private theorem shiftZeroList (ts : List InferT) : inferDeBruijnIncList 0 ts = ts := by
  cases ts with
  | nil => simp [inferDeBruijnIncList]
  | cons t ts => simp [inferDeBruijnIncList, shiftZeroType t, shiftZeroList ts]
termination_by sizeOf ts
end

/-- A zero shift leaves an inference type unchanged. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "infer_deBruijn_inc0"]
theorem inferDeBruijnInc0 (_n : Nat) (t : InferT) : inferDeBruijnInc 0 t = t :=
  shiftZeroType t

/-- A zero shift is the identity function. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "infer_deBruijn_inc0_id"]
theorem inferDeBruijnInc0Id : inferDeBruijnInc 0 = (fun t => t) := by
  funext t
  exact inferDeBruijnInc0 0 t

end Flapjack.Compiler.Inference.InferProps
