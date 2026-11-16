module

public import Flapjack.Compiler.Inference.Unify.WorklistVars
public import Flapjack.Misc.Bag

@[expose] public section

/-! The exact multiplicity bag used by the worklist termination measure. -/

namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

@[hol "cakeml/compiler/inference/unifyScript.sml" "PFLAT_def"]
noncomputable def pflat : List (List InferT × List InferT) → Bag (Term Atom)
  | [] => emptyBag
  | ([], []) :: rest => pflat rest
  | ([], y :: ys) :: rest => bagInsert (encodeInferT y) (pflat (([], ys) :: rest))
  | (x :: xs, ys) :: rest => bagInsert (encodeInferT x) (pflat ((xs, ys) :: rest))
termination_by work => sizeOf work
decreasing_by all_goals simp_wf <;> omega

@[hol "cakeml/compiler/inference/unifyScript.sml" "FINITE_BAG_PFLAT"]
theorem finitePflat (work : List (List InferT × List InferT)) : finiteBag (pflat work) := by
  fun_induction pflat work with
  | case1 => exact finiteEmptyBag
  | case2 rest ih => exact ih
  | case3 y ys rest ih => exact finiteBagInsert _ ih _
  | case4 x xs ys rest ih => exact finiteBagInsert _ ih _

end Flapjack.Compiler.Inference.Unify
