import Flapjack.Compiler.Backend.RegAlloc
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack arithmetic infrastructure for the local MOD_PLUS argument in
word_allocProofScript.sml:10312-10335. There is no separate named HOL theorem
for this numeric statement, so it is deliberately untagged. -/
theorem limitVarMultiple (maximum : Nat) :
    (maximum + (4 - maximum % 4)) % 4 = 0 := by
  omega

/-- Flapjack arithmetic infrastructure for the two branches of the local
limit_var_props proof (word_allocProofScript.sml:10299-10335). This has no
independent HOL theorem name and is not the full program theorem: its strict
bound is combined with native max_var_max by that later theorem. Every Nat
maximum, including multiples of four and unbounded values, is allowed. -/
theorem limitVarArithmetic (maximum : Nat) :
    isAllocVar (maximum + (4 - maximum % 4) + 1) ∧
      maximum < maximum + (4 - maximum % 4) + 1 := by
  constructor
  · unfold isAllocVar
    simp only [decide_eq_true_eq]
    omega
  · omega

end Flapjack.Compiler.Backend.WordAlloc
