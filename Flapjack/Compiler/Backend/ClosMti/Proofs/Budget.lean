import Flapjack.Compiler.Backend.ClosMti
import Flapjack.Compiler.Backend.ClosLang.Proofs.Budget

/-! Budget bounds for multi-argument collection. These are Flapjack
infrastructure lemmas, not HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang

private theorem listBudget_append (xs ys : List Exp) :
    listBudget (xs ++ ys) + 2 = listBudget xs + listBudget ys := by
  induction xs with
  | nil => simp [listBudget, Nat.add_comm]
  | cons x xs ih => simp only [List.cons_append, listBudget]; omega

/-- Collecting function arguments never increases the remaining body's budget. -/
theorem collectArgs_budget (maxApp n : Nat) (e : Exp) :
    expBudget (collectArgs maxApp n e).2 ≤ expBudget e := by
  cases e with
  | fn name loc fvs arity body =>
    cases loc with
    | some loc => simp [collectArgs]
    | none =>
      cases fvs with
      | some fvs => simp [collectArgs]
      | none =>
        simp only [collectArgs]
        split
        · have h := collectArgs_budget maxApp (n + arity) body
          simp only [expBudget]; omega
        · simp
  | _ => simp [collectArgs]
termination_by sizeOf e

/-- Collecting applications keeps the combined argument and head budget
within the original expression and accumulator budgets. -/
theorem collectApps_budget (maxApp : Nat) (args : List Exp) (e : Exp) :
    listBudget (collectApps maxApp args e).1 + expBudget (collectApps maxApp args e).2 ≤
      listBudget args + expBudget e := by
  cases e with
  | app t loc body more =>
    cases loc with
    | some loc => simp [collectApps]
    | none =>
      simp only [collectApps]
      split
      · have h := collectApps_budget maxApp (args ++ more) body
        have append := listBudget_append args more
        simp only [expBudget]
        omega
      · simp
  | _ => simp [collectApps]
termination_by sizeOf e

end Flapjack.Compiler.Backend.ClosMti
