module

public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Syntax

@[expose] public section

/-! Label preservation by let-operation cleanup. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosLang ClosProps

/-- A recognized operation is label-free exactly when its operator is. -/
private theorem destOp_noLabels {α : Type} (body : Exp) (args : List α) (op : Op)
    (h : destOp body args = some op) : noLabels body ↔ ∀ n, op ≠ .label n := by
  cases body <;> simp [destOp] at h
  case op trace opn xs =>
    have safe := (noLabelsList_iff xs).mpr (varList_noLabels 0 xs args 0 h.1).1
    rw [← h.2]
    simp [noLabels, safe]

mutual
/-- Singleton induction infrastructure for the HOL list theorem. -/
private theorem sing (e : Exp) :
    noLabels (compileSing e) ↔ noLabels e := by
  cases e with
  | var t n => simp [compileSing, noLabels]
  | ifThenElse t x y z => simp [compileSing, noLabels, sing x, sing y, sing z]
  | «let» t xs body =>
    simp only [compileSing]
    cases h : destOp (compileSing body) (compileList xs) with
    | none => simp [noLabels, many xs, sing body]
    | some op =>
      have safe := (sing body).symm.trans (destOp_noLabels _ _ _ h)
      simp [noLabels, many xs, ← safe, and_comm]
  | raise t x => simp [compileSing, noLabels, sing x]
  | handle t x y => simp [compileSing, noLabels, sing x, sing y]
  | tick t x => simp [compileSing, noLabels, sing x]
  | call t ticks dest xs => simp [compileSing, noLabels, many xs]
  | app t loc x xs => simp [compileSing, noLabels, sing x, many xs]
  | fn name loc vs arity body => simp [compileSing, noLabels, sing body]
  | letrec names loc vs fns body => simp [compileSing, noLabels, funs fns, sing body]
  | op t op xs => simp [compileSing, noLabels, many xs]
termination_by sizeOf e

/-- List induction infrastructure for the HOL list theorem. -/
private theorem many (xs : List Exp) :
    noLabelsList (compileList xs) ↔ noLabelsList xs := by
  cases xs with
  | nil => simp [compileList, noLabelsList]
  | cons x xs => simp [compileList, noLabelsList, sing x, many xs]
termination_by sizeOf xs

/-- Recursive-bundle induction infrastructure for the HOL list theorem. -/
private theorem funs (fns : List (Nat × Exp)) :
    noLabelsFuns (compileFuns fns) ↔ noLabelsFuns fns := by
  cases fns with
  | nil => simp [compileFuns, noLabelsFuns]
  | cons pair fns =>
    cases pair with
    | mk arity body => simp [compileFuns, noLabelsFuns, sing body, funs fns]
termination_by sizeOf fns
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- Let-operation cleanup preserves the full label-free predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "let_op_no_Labels"]
theorem compileSource_noLabels (xs : List Exp) :
    (∀ e ∈ compileSource xs, noLabels e) ↔
      ∀ e ∈ xs, noLabels e := by
  simpa only [compileSource_eq_list, ← noLabelsList_iff] using many xs

end Flapjack.Compiler.Backend.ClosLetop
