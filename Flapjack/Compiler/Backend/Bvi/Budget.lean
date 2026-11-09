import Flapjack.Compiler.Backend.Bvi.Syntax

/-! Computable structural budgets for BVI traversals. -/
namespace Flapjack.Compiler.Backend.Bvi

mutual
/-- A computable structural bound for expression lowering. -/
def expBudget : Exp → Nat
  | .var _ | .force _ _ => 1
  | .ifThenElse x y z => 1 + expBudget x + expBudget y + expBudget z
  | .let xs x => 1 + listBudget xs + expBudget x
  | .raise x | .tick x => 1 + expBudget x
  | .return xs | .op _ xs => 1 + listBudget xs
  | .call _ _ xs none => 1 + listBudget xs
  | .call _ _ xs (some h) => 1 + listBudget xs + expBudget h
  | .letCall _ _ _ xs x => 1 + listBudget xs + expBudget x
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega

/-- A computable structural bound for operand traversal. -/
def listBudget : List Exp → Nat
  | [] => 1
  | x :: xs => 1 + expBudget x + listBudget xs
termination_by xs => sizeOf xs
decreasing_by all_goals simp_wf <;> omega
end

/-- Flapjack infrastructure: an element's budget is below the list budget.
Shared by the BVI passes; no separately named HOL original. -/
theorem member_budget_lt (xs : List Bvi.Exp) (e : Bvi.Exp) (h : e ∈ xs) :
    expBudget e < listBudget xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [listBudget]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

end Flapjack.Compiler.Backend.Bvi
