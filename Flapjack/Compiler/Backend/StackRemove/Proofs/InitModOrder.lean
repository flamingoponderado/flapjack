import Flapjack.HolRef

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.InitModOrder

/-- Complete original natural-number modulus order implication. The sole
premise is the original conjunction; in particular, no divisor positivity
assumption is added, and the total zero-divisor case remains quantified. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "MOD_LESS_EQ_MOD_IMP"]
theorem modLessEqModImp (m k n : Nat) (bounds : m % k ≤ n ∧ m < k) : m ≤ n := by
  simpa only [Nat.mod_eq_of_lt bounds.2] using bounds.1

/-- Complete original divisibility witness: a zero remainder with a nonzero
divisor yields an exact quotient. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "MOD_EQ_IMP_MULT"]
theorem modEqImpMult : ∀ n d : Nat, n % d = 0 ∧ d ≠ 0 → ∃ k, n = d * k := by
  rintro n d ⟨zero, _⟩
  exact ⟨n / d, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero zero)).symm⟩

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitModOrder
