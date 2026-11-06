import Flapjack.Compiler.Backend.Bvl.Syntax

/-! Computable structural budgets for BVL-to-BVI lowering. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

mutual
/-- A bound that also covers the default expression produced by `destLet`. -/
def expBudget : Bvl.Exp → Nat
  | .var _ | .force _ _ => 2
  | .ifThenElse x y z => 2 + expBudget x + expBudget y + expBudget z
  | .let xs body => 2 + listBudget xs + expBudget body
  | .raise x | .tick x => 2 + expBudget x
  | .handle x y => 2 + expBudget x + expBudget y
  | .call _ _ xs | .op _ xs => 2 + listBudget xs
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega

/-- A bound for a list of operands, including the empty-list case. -/
def listBudget : List Bvl.Exp → Nat
  | [] => 2
  | x :: xs => 2 + expBudget x + listBudget xs
termination_by xs => sizeOf xs
decreasing_by all_goals simp_wf <;> omega
end

end Flapjack.Compiler.Backend.BvlToBvi
