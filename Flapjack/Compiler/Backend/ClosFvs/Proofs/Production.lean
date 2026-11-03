import Flapjack.Compiler.Backend.ClosFvs.Source
import Flapjack.Compiler.Backend.ClosFvs.Proofs.Total
import Mathlib.Tactic

/-! Agreement of the executed retry with source-shaped free-variable removal. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open ClosLang

/-- The list traversal is the pointwise source traversal. -/
theorem removeList_eq_map (bound : Nat) (expressions : List Exp) :
    removeList bound expressions = expressions.map (removeSing bound) := by
  induction expressions with
  | nil => rfl
  | cons first rest ih => simp [removeList, ih]

/-- The recursive bundle traversal preserves arities and source order. -/
theorem removeFuns_eq_map (count captured : Nat) (functions : List (Nat × Exp)) :
    removeFuns count captured functions =
      functions.map (fun (arity, body) => (arity, removeSing (arity + count + captured) body)) := by
  induction functions with
  | nil => rfl
  | cons function rest ih =>
    obtain ⟨arity, body⟩ := function
    simp [removeFuns, ih]

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

/-- Every successful bounded traversal agrees with the total source traversal. -/
theorem removeFuel_eq_source (fuel bound : Nat) (expression result : Exp)
    (run : removeFuel fuel bound expression = some result) : result = removeSing bound expression := by
  induction fuel generalizing bound expression result with
  | zero => simp [removeFuel] at run
  | succ fuel ih =>
    cases expression
    case «let» trace xs body =>
      cases xsRun : xs.mapM (removeFuel fuel bound) with
      | none => simp [removeFuel, xsRun] at run
      | some ys =>
        cases bodyRun : removeFuel fuel (bound + ys.length) body with
        | none => simp [removeFuel, xsRun, bodyRun] at run
        | some nextBody =>
          have ysEq := mapM_eq_map (removeFuel fuel bound) (removeSing bound) (ih bound) xs ys xsRun
          have bodyEq := ih (bound + ys.length) body nextBody bodyRun
          simp [removeFuel, xsRun, bodyRun] at run
          subst result
          simp [removeSing, removeList_eq_map, ← ysEq, bodyEq]
    all_goals simp only [removeFuel] at run
    all_goals simp only [removeSing]
    all_goals try (simp only [bind, Option.bind] at run)
    all_goals repeat' split at run
    all_goals try simp_all [removeList_eq_map, removeFuns_eq_map]
    all_goals aesop (add safe apply mapM_eq_map)

/-- The production retry always returns the source traversal. -/
theorem removeBounded_eq_source (fuel bound : Nat) (expression : Exp) :
    removeBounded fuel bound expression = some (removeSing bound expression) := by
  obtain ⟨result, run⟩ := removeBounded_succeeds fuel bound expression
  unfold removeBounded at run ⊢
  cases first : removeFuel fuel bound expression with
  | some value =>
    have equal := removeFuel_eq_source fuel bound expression value first
    simp [equal]
  | none =>
    have retry : removeFuel (max fuel (expBudget expression + 1)) bound expression = some result := by
      simpa [first] using run
    have equal := removeFuel_eq_source _ bound expression result retry
    simpa [first, equal] using retry

/-- The production list traversal agrees with the original list pass. -/
theorem removeBounded_list_eq_source (fuel bound : Nat) (expressions : List Exp) :
    expressions.mapM (removeBounded fuel bound) = some (removeList bound expressions) := by
  induction expressions with
  | nil => rfl
  | cons first rest ih =>
    simp [removeList, removeBounded_eq_source, ih]

end Flapjack.Compiler.Backend.ClosFvs
