import Flapjack.EvaluateHOL
import Lean.Elab.Tactic.Omega

/-! Termination support for the source evaluator. These Lean-specific lemmas
have no separate HOL declaration: the original termination proof uses a
lexicographic clock and expression-list size measure. -/
namespace Flapjack.EvaluateHOL
open Flapjack.SemanticPrimitivesHOL

/-- Lean's list size is additive up to the empty-list constructor. -/
theorem listSize_append {α : Type} [SizeOf α] (xs ys : List α) :
    sizeOf (xs ++ ys) + 1 = sizeOf xs + sizeOf ys := by
  induction xs with
  | nil => simp; omega
  | cons x xs ih => simp_all; omega

/-- Reversing argument evaluation order preserves the termination measure. -/
theorem listSize_reverse {α : Type} [SizeOf α] (xs : List α) :
    sizeOf xs.reverse = sizeOf xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons]
    have h := listSize_append xs.reverse [x]
    simp_all
    omega

/-- Source expression and declaration constructors have positive size. -/
theorem expSize_pos (expr : Flapjack.AstHOL.Exp) : 0 < sizeOf expr := by
  cases expr <;> simp_wf <;> omega

theorem decSize_pos (decl : Flapjack.AstHOL.Dec) : 0 < sizeOf decl := by
  cases decl <;> simp_wf <;> omega

theorem patSize_pos (pat : Flapjack.AstHOL.Pat) : 0 < sizeOf pat := by
  cases pat <;> simp_wf <;> omega

theorem listSize_pos {α : Type} [SizeOf α] (xs : List α) : 0 < sizeOf xs := by
  cases xs <;> simp_wf <;> omega

theorem doIf_selected {α : Type} (v : Value) (a b result : α)
    (h : doIf v a b = some result) : result = a ∨ result = b := by
  unfold doIf at h
  split at h <;> simp_all

theorem doLog_selected (op : Flapjack.AstHOL.Lop) (v : Value)
    (expr result : Flapjack.AstHOL.Exp) (h : doLog op v expr = some (.exp result)) : result = expr := by
  unfold doLog at h
  split at h <;> simp_all

end Flapjack.EvaluateHOL
