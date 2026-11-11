module

public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Syntax

@[expose] public section

/-! Application-arity preservation by let-operation cleanup. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosLang ClosProps

/-- Recognition implies the operation body meets every arity bound. -/
private theorem destOp_obeysMaxApp {α : Type} (body : Exp) (args : List α) (op : Op)
    (limit : Nat) (h : destOp body args = some op) : obeysMaxApp limit body := by
  cases body <;> simp [destOp] at h
  case op trace opn xs =>
    simpa only [obeysMaxApp] using
      (obeysMaxAppList_iff limit xs).mpr (varList_noLabels 0 xs args limit h.1).2

mutual
/-- Singleton induction infrastructure for the HOL list theorem. -/
private theorem sing (e : Exp) (limit : Nat) :
    obeysMaxApp limit (compileSing e) ↔ obeysMaxApp limit e := by
  cases e with
  | var t n => simp [compileSing, obeysMaxApp]
  | ifThenElse t x y z => simp [compileSing, obeysMaxApp, sing x, sing y, sing z]
  | «let» t xs body =>
    simp only [compileSing]
    cases h : destOp (compileSing body) (compileList xs) with
    | none => simp [obeysMaxApp, many xs, sing body]
    | some op =>
      have safe := destOp_obeysMaxApp _ _ _ limit h
      have original := (sing body limit).mp safe
      simp [obeysMaxApp, many xs, original]
  | raise t x => simp [compileSing, obeysMaxApp, sing x]
  | handle t x y => simp [compileSing, obeysMaxApp, sing x, sing y]
  | tick t x => simp [compileSing, obeysMaxApp, sing x]
  | call t ticks dest xs => simp [compileSing, obeysMaxApp, many xs]
  | app t loc x xs => simp [compileSing, obeysMaxApp, compileList_length, sing x, many xs]
  | fn name loc vs arity body => simp [compileSing, obeysMaxApp, sing body]
  | letrec names loc vs fns body => simp [compileSing, obeysMaxApp, funs fns, sing body]
  | op t op xs => simp [compileSing, obeysMaxApp, many xs]
termination_by sizeOf e

/-- List induction infrastructure for the HOL list theorem. -/
private theorem many (xs : List Exp) (limit : Nat) :
    obeysMaxAppList limit (compileList xs) ↔ obeysMaxAppList limit xs := by
  cases xs with
  | nil => simp [compileList, obeysMaxAppList]
  | cons x xs => simp [compileList, obeysMaxAppList, sing x, many xs]
termination_by sizeOf xs

/-- Recursive-bundle induction infrastructure for the HOL list theorem. -/
private theorem funs (fns : List (Nat × Exp)) (limit : Nat) :
    obeysMaxAppFuns limit (compileFuns fns) ↔ obeysMaxAppFuns limit fns := by
  cases fns with
  | nil => simp [compileFuns, obeysMaxAppFuns]
  | cons pair fns =>
    cases pair with
    | mk arity body => simp [compileFuns, obeysMaxAppFuns, sing body, funs fns]
termination_by sizeOf fns
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- Let-operation cleanup preserves the full application-arity predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "let_op_obeys_max_app"]
theorem compileSource_obeysMaxApp (limit : Nat) (xs : List Exp) :
    (∀ e ∈ compileSource xs, obeysMaxApp limit e) ↔
      ∀ e ∈ xs, obeysMaxApp limit e := by
  simpa only [compileSource_eq_list, ← obeysMaxAppList_iff] using many xs limit

end Flapjack.Compiler.Backend.ClosLetop
