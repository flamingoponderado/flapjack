import Flapjack.Compiler.Backend.Semantics.BvlSem.Apply
import Flapjack.Compiler.Backend.Semantics.BvlSem.Call
import Lean.Elab.Tactic.Omega

/-! Expression weights used to define the clocked BVL evaluator. -/
namespace Flapjack.Compiler.Backend.BvlSem

mutual
/-- Structural weight of a BVL expression. -/
def expWeight : Bvl.Exp → Nat
  | .var _ | .force _ _ => 1
  | .ifThenElse a b c => 1 + expWeight a + expWeight b + expWeight c
  | .let xs body => 1 + expsWeight xs + expWeight body
  | .raise body | .tick body => 1 + expWeight body
  | .handle body handler => 1 + expWeight body + expWeight handler
  | .call _ _ xs | .op _ xs => 1 + expsWeight xs
termination_by exp => sizeOf exp

/-- Structural weight of a list of BVL expressions. -/
def expsWeight : List Bvl.Exp → Nat
  | [] => 0
  | e :: rest => 1 + expWeight e + expsWeight rest
termination_by exps => sizeOf exps
end

/-- Every BVL expression has positive structural weight. -/
theorem expWeight_pos (exp : Bvl.Exp) : 0 < expWeight exp := by
  cases exp <;> simp [expWeight] <;> omega

end Flapjack.Compiler.Backend.BvlSem
