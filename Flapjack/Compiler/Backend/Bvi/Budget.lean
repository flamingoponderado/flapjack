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

end Flapjack.Compiler.Backend.Bvi
