module

public import Flapjack.Compiler.Inference.Unify.Encoding
public import Flapjack.HOL.Unification.Term.Finite

@[expose] public section

/-! Variables measured by the source unification worklist relation. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

@[hol "cakeml/compiler/inference/unifyScript.sml" "isvars_def"]
def isvars : List InferT → Set Nat
  | [] => ∅
  | t :: ts => Set.union (vars (encodeInferT t)) (isvars ts)

@[hol "cakeml/compiler/inference/unifyScript.sml" "FINITE_isvars"]
theorem finiteIsvars (ts : List InferT) : (isvars ts).Finite := by
  induction ts with
  | nil => exact Set.finite_empty
  | cons t ts ih => exact (finiteVars (encodeInferT t)).union ih

@[hol "cakeml/compiler/inference/unifyScript.sml" "cplist_vars_def"]
def cplistVars : List (List InferT × List InferT) → Set Nat
  | [] => ∅
  | (ts, us) :: rest => Set.union (Set.union (isvars ts) (isvars us)) (cplistVars rest)

@[hol "cakeml/compiler/inference/unifyScript.sml" "FINITE_cplist_vars"]
theorem finiteCplistVars (wl : List (List InferT × List InferT)) : (cplistVars wl).Finite := by
  induction wl with
  | nil => exact Set.finite_empty
  | cons pair rest ih =>
    rcases pair with ⟨ts, us⟩
    exact ((finiteIsvars ts).union (finiteIsvars us)).union ih

@[hol "cakeml/compiler/inference/unifyScript.sml" "vars_encode_infer_ts"]
theorem varsEncodeInferTs (ts : List InferT) : vars (encodeInferTs ts) = isvars ts := by
  induction ts with
  | nil =>
    funext v
    apply propext
    simp only [encodeInferTs, vars, isvars]
    change False ↔ False
    rfl
  | cons t ts ih =>
    funext v
    apply propext
    simp only [encodeInferTs, vars, isvars]
    change (vars (encodeInferT t) v ∨ vars (encodeInferTs ts) v) ↔
      (vars (encodeInferT t) v ∨ isvars ts v)
    rw [ih]

end Flapjack.Compiler.Inference.Unify
