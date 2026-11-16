module

public import Flapjack.Compiler.Inference.Unify.ComputationalWalk.Order
public import Flapjack.Compiler.Inference.Unify.WorklistBag
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! The source-shaped occurs-check step and its multiset measure. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- The source worklist step using the selected total walker. This is not
    tagged as the unconditional HOL definition: the tail-recursion choices can
    differ outside the original `cwfs` guard. -/
noncomputable def kcocwlCodeModel (s : Spt InferT) (n : Nat) :
    List (List InferT) → Sum (List (List InferT)) Bool
  | [] => .inr false
  | [] :: rest => .inl rest
  | (i :: tail) :: rest =>
    match tcwalkModel s i with
    | .varDb _ => .inl (tail :: rest)
    | .app args _ => .inl (args :: tail :: rest)
    | .uvar v => if n = v then .inr true else .inl (tail :: rest)

/-- The original multiset-then-length measure. It is untagged because the
    finite-map producer occurs in the body rather than the signature, outside
    the current result-observation qualifier. -/
def kcocwlRModel (s : Spt InferT) (_n : Nat) (child parent : List (List InferT)) : Prop :=
  let childBag := bagOfList (child.flatten.map encodeInferT)
  let parentBag := bagOfList (parent.flatten.map encodeInferT)
  bagMultisetStep (walkstarR (sp2fm (sptMap encodeInferT s))) childBag parentBag ∨
    (childBag = parentBag ∧ child.length < parent.length)

@[hol "cakeml/compiler/inference/unifyScript.sml" "kcocwl_preserves_precond"]
theorem kcocwlPreservesPrecondModel (s : Spt InferT) (n : Nat) : ∀ x y,
    (fun _ : List (List InferT) => cwfs s) x ∧ kcocwlCodeModel s n x = .inl y →
      (fun _ : List (List InferT) => cwfs s) y := by
  intro x y h
  exact h.1

private theorem finiteBagOfList {α : Type} (xs : List α) : finiteBag (bagOfList xs) := by
  apply (finiteBagFoldrInsert xs emptyBag).2
  exact finiteEmptyBag

private theorem bagOfListAppend {α : Type} (xs ys : List α) :
    bagOfList (xs ++ ys) = bagUnion (bagOfList xs) (bagOfList ys) := by
  unfold bagOfList
  rw [List.foldr_append, foldrBagInsertUnion]
  funext e
  simp [bagUnion, Nat.add_comm, bagOfList]

private theorem bagWorkCons (xs : List InferT) (rest : List (List InferT)) :
    bagOfList (((xs :: rest).flatten).map encodeInferT) =
      bagUnion (bagOfList (xs.map encodeInferT)) (bagOfList (rest.flatten.map encodeInferT)) := by
  simp only [List.flatten_cons, List.map_append]
  exact bagOfListAppend _ _

private theorem bagWorkHead (i : InferT) (xs : List InferT) (rest : List (List InferT)) :
    bagOfList ((((i :: xs) :: rest).flatten).map encodeInferT) =
      bagInsert (encodeInferT i) (bagOfList (((xs :: rest).flatten).map encodeInferT)) := by
  rw [bagWorkCons, bagWorkCons]
  simp only [List.map_cons, bagOfList, List.foldr_cons]
  exact (bagUnionInsert _ _ _).1

private theorem tailDecrease (s : Spt InferT) (n : Nat) (i : InferT)
    (xs : List InferT) (rest : List (List InferT)) :
    kcocwlRModel s n (xs :: rest) ((i :: xs) :: rest) := by
  left
  rw [bagWorkHead]
  exact mlt1BagInsert _ _ _ (finiteBagOfList _)

private theorem appDecrease (s : Spt InferT) (n : Nat) (i : InferT)
    (args xs : List InferT) (name : Nat) (rest : List (List InferT))
    (hw : cwfs s) (hwalk : tcwalkModel s i = .app args name) :
    kcocwlRModel s n (args :: xs :: rest) ((i :: xs) :: rest) := by
  left
  refine ⟨finiteBagOfList _, finiteBagOfList _, encodeInferT i,
    bagOfList (args.map encodeInferT), bagOfList (((xs :: rest).flatten).map encodeInferT),
    bagWorkCons args (xs :: rest), ?_, ?_⟩
  · rw [bagWorkHead]
    classical
    funext e
    by_cases h : e = encodeInferT i <;> simp [bagUnion, bagInsert, emptyBag, h]
  · intro e he
    have mem : e ∈ args.map encodeInferT := (bagInBagOfList e _).mp he
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp mem
    exact walkstarOpthModel s i i0 args name ⟨hw, hwalk, hi0⟩

/-- Complete source-shaped decrease result for every occurs-check transition.
    The conclusion unfolds the source relation to expose its observed finite map.
    The selected source-step model is used under the original `cwfs` guard. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "kcocwl_ensures_decrease"
  (fmap_as_finite_support_result_observations := [Flapjack.HOL.Transfer.Fmsp.sp2fm])]
theorem kcocwlEnsuresDecreaseModel (s : Spt InferT) (n : Nat) : ∀ x y,
    (fun _ : List (List InferT) => cwfs s) x ∧ kcocwlCodeModel s n x = .inl y →
      (bagMultisetStep (walkstarR (sp2fm (sptMap encodeInferT s)))
          (bagOfList (y.flatten.map encodeInferT)) (bagOfList (x.flatten.map encodeInferT)) ∨
        (bagOfList (y.flatten.map encodeInferT) = bagOfList (x.flatten.map encodeInferT) ∧
          y.length < x.length)) := by
  intro x y ⟨hw, step⟩
  change kcocwlRModel s n y x
  cases x with
  | nil => simp [kcocwlCodeModel] at step
  | cons head rest =>
    cases head with
    | nil =>
      simp only [kcocwlCodeModel, Sum.inl.injEq] at step
      subst y
      right
      simp
    | cons i xs =>
      cases hwalk : tcwalkModel s i with
      | varDb k =>
        simp [kcocwlCodeModel, hwalk] at step
        subst y
        exact tailDecrease s n i xs rest
      | app args name =>
        simp [kcocwlCodeModel, hwalk] at step
        subst y
        exact appDecrease s n i args xs name rest hw hwalk
      | uvar v =>
        by_cases eq : n = v
        · simp [kcocwlCodeModel, hwalk, eq] at step
        · simp [kcocwlCodeModel, hwalk, eq] at step
          subst y
          exact tailDecrease s n i xs rest

end Flapjack.Compiler.Inference.Unify
