import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.BvlSem.Call
import Lean.Elab.Tactic.Omega

/-! Structural weights for the clocked BVI evaluator. -/
namespace Flapjack.Compiler.Backend.BviSem

mutual
/-- Structural weight of a BVI expression. -/
def expWeight : Bvi.Exp → Nat
  | .var _ | .force _ _ => 1
  | .ifThenElse a b c => 1 + expWeight a + expWeight b + expWeight c
  | .let xs body => 1 + expsWeight xs + expWeight body
  | .raise body | .tick body => 1 + expWeight body
  | .call _ _ xs none => 1 + expsWeight xs
  | .call _ _ xs (some handler) => 1 + expsWeight xs + expWeight handler
  | .op _ xs | .return xs => 1 + expsWeight xs
  | .letCall _ _ _ xs body => 1 + expsWeight xs + expWeight body
termination_by exp => sizeOf exp

/-- Structural weight of a list of BVI expressions. -/
def expsWeight : List Bvi.Exp → Nat
  | [] => 0
  | e :: rest => 1 + expWeight e + expsWeight rest
termination_by exps => sizeOf exps
end

/-- Every BVI expression has positive structural weight. -/
theorem expWeight_pos (exp : Bvi.Exp) : 0 < expWeight exp := by
  cases exp <;> try (simp [expWeight] <;> omega)
  case call ticks dest args handler => cases handler <;> simp [expWeight] <;> omega

end Flapjack.Compiler.Backend.BviSem
