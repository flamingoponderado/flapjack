import Flapjack.Compiler.Backend.BvlInline.Proofs.TraversalTotal
import Flapjack.Compiler.Backend.Semantics.BvlSem.Measure
import Flapjack.HolRef
import Aesop

/-! Total source-shaped BVL tick removal and its executable correspondence. -/
namespace Flapjack.Compiler.Backend.BvlInline
open BvlSem

mutual
/-- Remove tick accounting from one expression. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "remove_ticks_sing_def"]
def removeTicksSing : Bvl.Exp → Bvl.Exp
  | .var n => .var n
  | .ifThenElse a b c => .ifThenElse (removeTicksSing a) (removeTicksSing b) (removeTicksSing c)
  | .let xs body => .let (removeTicksList xs) (removeTicksSing body)
  | .raise body => .raise (removeTicksSing body)
  | .handle body handler => .handle (removeTicksSing body) (removeTicksSing handler)
  | .tick body => removeTicksSing body
  | .force location index => .force location index
  | .op op xs => .op op (removeTicksList xs)
  | .call _ dest xs => .call 0 dest (removeTicksList xs)
termination_by expression => sizeOf expression

/-- Remove tick accounting from a list of expressions. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "remove_ticks_sing_def"]
def removeTicksList : List Bvl.Exp → List Bvl.Exp
  | [] => []
  | e :: es => removeTicksSing e :: removeTicksList es
termination_by expressions => sizeOf expressions
end

/-- List form of tick removal; the mutual traversal satisfies the original
list and singleton equations and has the same result for every input. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "remove_ticks_def"]
def removeTicks (expressions : List Bvl.Exp) : List Bvl.Exp := removeTicksList expressions

/-- The single-expression and list traversals agree with tick removal. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "remove_ticks_sing"]
theorem removeTicksSing_equivalence :
    (∀ expression, removeTicks [expression] = [removeTicksSing expression]) ∧
      (∀ expressions, removeTicksList expressions = removeTicks expressions) := by
  constructor
  · intro expression; simp [removeTicks, removeTicksList]
  · intro expressions; rfl

/-- The source list recursion and singleton tick/call cases hold for the
total representation. Other singleton constructor equations follow by the
same unfolding of the mutual traversal. -/
theorem removeTicks_source_cases (first second body : Bvl.Exp) (tail args : List Bvl.Exp)
    (ticks : Nat) (destination : Option Nat) :
    removeTicks [] = [] ∧
    removeTicks (first :: second :: tail) =
      removeTicksSing first :: removeTicks (second :: tail) ∧
    removeTicks [.tick body] = removeTicks [body] ∧
    removeTicks [.call ticks destination args] = [.call 0 destination (removeTicks args)] := by
  simp [removeTicks, removeTicksList, removeTicksSing]

/-- The list traversal is the map of the corresponding single-expression traversal. -/
theorem removeTicksList_eq_map (expressions : List Bvl.Exp) :
    removeTicksList expressions = expressions.map removeTicksSing := by
  induction expressions with
  | nil => simp [removeTicksList]
  | cons first rest ih => simp [removeTicksList, ih]

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

/-- Any successful fuel-bounded run agrees with the total source traversal. -/
theorem removeTicksFuel_eq (fuel : Nat) (expression result : Bvl.Exp)
    (run : removeTicksFuel fuel expression = some result) : result = removeTicksSing expression := by
  induction fuel generalizing expression result with
  | zero => simp [removeTicksFuel] at run
  | succ fuel ih =>
    cases expression <;> simp only [removeTicksFuel] at run <;>
      simp only [removeTicksSing]
    all_goals try (simp only [bind, Option.bind] at run)
    all_goals repeat' split at run
    all_goals try simp_all [removeTicksList_eq_map]
    all_goals aesop (add safe apply mapM_eq_map)

/-- The production bounded traversal always returns the total source result. -/
theorem removeTicksBounded_eq (fuel : Nat) (expression : Bvl.Exp) :
    removeTicksBounded fuel expression = some (removeTicksSing expression) := by
  cases first : removeTicksFuel fuel expression with
  | some result =>
    have correct := removeTicksFuel_eq fuel expression result first
    simp [removeTicksBounded, first, correct]
  | none =>
    have bound : BvlToBvi.expBudget expression < max fuel (BvlToBvi.expBudget expression + 1) := by omega
    obtain ⟨result, run⟩ := removeTicksFuel_succeeds _ expression bound
    have correct := removeTicksFuel_eq _ expression result run
    simp [removeTicksBounded, first, run, correct]

end Flapjack.Compiler.Backend.BvlInline
