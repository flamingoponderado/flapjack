module

public import Flapjack.Compiler.Inference.Unify.WorklistVars
public import Flapjack.Misc.Bag
public import Flapjack.Misc.Bag.SubBag
public import Flapjack.Misc.Bag.MultisetOrder

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

private theorem subBagInsert {α : Type} (b : Bag α) (e : α) :
    subBag b (bagInsert e b) := by
  classical
  intro x n hn
  by_cases hx : x = e <;> simp [bagInn, bagInsert, hx] at hn ⊢ <;> omega

@[hol "cakeml/compiler/inference/unifyScript.sml" "FINITE_BAG_FOLDR_INSERT"]
theorem finiteBagFoldrInsert {α : Type} (xs : List α) (b : Bag α) :
    finiteBag (xs.foldr bagInsert b) ↔ finiteBag b := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change finiteBag (bagInsert x (xs.foldr bagInsert b)) ↔ finiteBag b
    rw [← ih]
    constructor
    · intro h
      exact finiteSubBag _ h _ (subBagInsert _ x)
    · intro h
      exact finiteBagInsert _ h x

/-- Finite list bags support the source worklist decrease proofs. -/
theorem finiteBagOfList {α : Type} (xs : List α) : finiteBag (bagOfList xs) :=
  (finiteBagFoldrInsert xs emptyBag).2 finiteEmptyBag

@[hol "cakeml/compiler/inference/unifyScript.sml" "mlt_BAG_INSERT2"]
theorem mltBagInsert2 {α : Type} (r : α → α → Prop) (b : Bag α) (x y : α)
    (h : finiteBag b) :
    Relation.TransGen (bagMultisetStep r) b (bagInsert x (bagInsert y b)) := by
  exact (Relation.TransGen.single (mlt1BagInsert r b y h)).tail
    (mlt1BagInsert r (bagInsert y b) x (finiteBagInsert b h y))

@[hol "cakeml/compiler/inference/unifyScript.sml" "FOLDR_BAG_INSERT_UNION"]
theorem foldrBagInsertUnion {α : Type} (xs : List α) (b : Bag α) :
    xs.foldr bagInsert b = bagUnion b (bagOfList xs) := by
  induction xs with
  | nil => exact (bagUnion_empty_right b).symm
  | cons x xs ih =>
    change bagInsert x (xs.foldr bagInsert b) =
      bagUnion b (bagInsert x (bagOfList xs))
    rw [ih, (bagUnionInsert x b (bagOfList xs)).2]

@[hol "cakeml/compiler/inference/unifyScript.sml" "BAG_IN_BAG_OF_LIST"]
theorem bagInBagOfList {α : Type} (e : α) (xs : List α) :
    bagIn e (bagOfList xs) ↔ e ∈ xs := by
  classical
  induction xs with
  | nil => simp [bagOfList, bagIn, bagInn, emptyBag]
  | cons x xs ih =>
    simp only [bagOfList, List.foldr_cons, List.mem_cons] at ih ⊢
    by_cases h : e = x
    · simp [bagIn, bagInn, bagInsert, h]
    · simp [bagIn, bagInn, bagInsert, h] at ih ⊢
      exact ih

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
