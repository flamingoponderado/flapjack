import Flapjack.Compiler.Backend.ClosLang.Syntax

/-! Computable structural budgets for closure-language traversals. -/
namespace Flapjack.Compiler.Backend.ClosLang

mutual
/-- A bound for traversing a closure expression. -/
def expBudget : Exp → Nat
  | .var _ _ => 2
  | .ifThenElse _ x y z => 2 + expBudget x + expBudget y + expBudget z
  | .let _ xs body => 2 + listBudget xs + expBudget body
  | .raise _ x | .tick _ x => 2 + expBudget x
  | .handle _ x y => 2 + expBudget x + expBudget y
  | .op _ _ xs | .call _ _ _ xs => 2 + listBudget xs
  | .app _ _ x xs => 2 + expBudget x + listBudget xs
  | .fn _ _ _ _ body => 2 + expBudget body
  | .letrec _ _ _ fns body => 2 + funsBudget fns + expBudget body
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega

/-- A bound for traversing an expression list. -/
def listBudget : List Exp → Nat
  | [] => 2
  | x :: xs => 2 + expBudget x + listBudget xs
termination_by xs => sizeOf xs
decreasing_by all_goals simp_wf <;> omega

/-- A bound for traversing recursive function bodies. -/
def funsBudget : List (Nat × Exp) → Nat
  | [] => 2
  | (_, body) :: xs => 2 + expBudget body + funsBudget xs
termination_by xs => sizeOf xs
decreasing_by all_goals simp_wf <;> omega
end

end Flapjack.Compiler.Backend.ClosLang
