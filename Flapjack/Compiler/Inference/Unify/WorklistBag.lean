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

@[hol "cakeml/compiler/inference/unifyScript.sml" "PFLAT_CONS2"]
theorem pflatCons2 (l1 : List InferT) (h2 : InferT) (t2 : List InferT)
    (rest : List (List InferT × List InferT)) :
    pflat ((l1, h2 :: t2) :: rest) =
      bagInsert (encodeInferT h2) (pflat ((l1, t2) :: rest)) := by
  induction l1 with
  | nil => rw [pflat]
  | cons x xs ih =>
    rw [pflat, pflat, ih, bagInsertCommutes]

/-- The source `BAG_OF_LIST` overload, a right fold of bag insertion. -/
noncomputable def bagOfList {α : Type} (xs : List α) : Bag α :=
  xs.foldr bagInsert emptyBag

@[hol "cakeml/compiler/inference/unifyScript.sml" "PFLAT_NIL1"]
theorem pflatNil1 (l2 : List InferT) (rest : List (List InferT × List InferT)) :
    pflat (([], l2) :: rest) =
      bagUnion (bagOfList (l2.map encodeInferT)) (pflat rest) := by
  induction l2 with
  | nil =>
    funext x
    simp [pflat, bagOfList, bagUnion, emptyBag]
  | cons y ys ih =>
    rw [pflat, ih]
    simp only [List.map_cons, bagOfList, List.foldr_cons]
    exact (bagUnionInsert _ _ _).1.symm

@[hol "cakeml/compiler/inference/unifyScript.sml" "PFLAT_eqn"]
theorem pflatEqn (l1 l2 : List InferT) (rest : List (List InferT × List InferT)) :
    pflat ((l1, l2) :: rest) =
      bagUnion (bagOfList (l1.map encodeInferT))
        (bagUnion (bagOfList (l2.map encodeInferT)) (pflat rest)) := by
  induction l1 with
  | nil =>
    rw [pflatNil1]
    funext x
    simp [bagOfList, bagUnion, emptyBag]
  | cons x xs ih =>
    rw [pflat, ih]
    simp only [List.map_cons, bagOfList, List.foldr_cons]
    exact (bagUnionInsert _ _ _).1.symm

end Flapjack.Compiler.Inference.Unify
