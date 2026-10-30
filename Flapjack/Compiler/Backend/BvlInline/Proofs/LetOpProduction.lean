import Flapjack.Compiler.Backend.BvlInline.Proofs.LetOp
import Flapjack.Compiler.Backend.BvlInline.Proofs.TraversalTotal
import Flapjack.Compiler.Backend.BvlInline.TickInline

/-! Executable correspondence for BVL let-operation optimization. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl

/-- The original recursive variable test equals the indexed implementation,
including mismatched lengths. This helper has no standalone HOL declaration. -/
theorem varListHOL_eq_indexed {α : Type} (n : Nat) (xs : List Exp) (ys : List α) :
    varListHOL n xs ys =
      (xs.length == ys.length && (xs.zip (List.range' n ys.length)).all fun (x, i) =>
        match x with | .var m => m == i | _ => false) := by
  induction xs generalizing n ys with
  | nil => cases ys <;> simp [varListHOL]
  | cons x xs ih =>
    cases ys with
    | nil => cases x <;> simp [varListHOL]
    | cons y ys =>
      cases x <;> simp [varListHOL, List.range'_succ, ih,
        Bool.and_comm, Bool.and_left_comm]

/-- The production variable-list test agrees with HOL for any argument list. -/
theorem varList_eq_HOL {α : Type} (xs : List Exp) (ys : List α) :
    varList xs ys.length = varListHOL 0 xs ys := by
  rw [varListHOL_eq_indexed]
  simp only [varList, List.range_eq_range']
  congr 1

/-- The source list traversal is a map of its one-expression traversal. -/
theorem letOpList_eq_map (expressions : List Exp) : letOpList expressions = expressions.map letOpOne := by
  induction expressions with
  | nil => simp [letOpList]
  | cons head tail ih => simp [letOpList, ih]

private theorem mapM_eq_map {α β : Type} (visit : α → Option β) (f : α → β)
    (correct : ∀ x y, visit x = some y → y = f x) (xs : List α) (ys : List β)
    (run : xs.mapM visit = some ys) : ys = xs.map f := by
  induction xs generalizing ys with
  | nil => simpa using run.symm
  | cons x rest ih =>
    simp only [List.mapM_cons] at run
    cases first : visit x with
    | none => simp [first] at run
    | some value =>
      cases remaining : rest.mapM visit with
      | none => simp [first, remaining] at run
      | some values =>
        simp [first, remaining] at run
        subst ys
        simp [correct x value first, ih values remaining]

/-- Every successful fuel-bounded traversal agrees with the original total
traversal. This correspondence has no standalone HOL declaration. -/
theorem letOpFuel_eq (fuel : Nat) (expression result : Exp)
    (run : letOpFuel fuel expression = some result) : result = letOpOne expression := by
  induction fuel generalizing expression result with
  | zero => simp [letOpFuel] at run
  | succ fuel ih =>
    cases expression
    case «let» xs body =>
      simp only [letOpFuel, bind, Option.bind] at run
      cases xsRun : xs.mapM (letOpFuel fuel) with
      | none => simp [xsRun] at run
      | some values =>
        cases bodyRun : letOpFuel fuel body with
        | none => simp [xsRun, bodyRun] at run
        | some bodyResult =>
          have valuesEq := mapM_eq_map (letOpFuel fuel) letOpOne ih xs values xsRun
          have bodyEq := ih body bodyResult bodyRun
          subst values
          subst bodyResult
          simp only [xsRun, bodyRun, letOpOne, letOpList_eq_map, destOp,
            ← varList_eq_HOL] at run ⊢
          cases h : letOpOne body <;> simp_all
          all_goals split at run <;> simp_all
    all_goals simp only [letOpFuel] at run
    all_goals try simp only [letOpOne]
    all_goals try (simp only [bind, Option.bind] at run)
    all_goals repeat' split at run
    all_goals try simp_all [letOpList_eq_map]
    all_goals aesop (add safe apply mapM_eq_map)

/-- The executed bounded traversal always produces the original result. -/
theorem letOpBounded_eq (fuel : Nat) (expression : Exp) :
    letOpBounded fuel expression = some (letOpOne expression) := by
  cases first : letOpFuel fuel expression with
  | some result =>
    have correct := letOpFuel_eq fuel expression result first
    simp [letOpBounded, first, correct]
  | none =>
    have bound : BvlToBvi.expBudget expression < max fuel (BvlToBvi.expBudget expression + 1) := by omega
    obtain ⟨result, run⟩ := letOpFuel_succeeds _ expression bound
    have correct := letOpFuel_eq _ expression result run
    simp [letOpBounded, first, run, correct]

end Flapjack.Compiler.Backend.BvlInline
