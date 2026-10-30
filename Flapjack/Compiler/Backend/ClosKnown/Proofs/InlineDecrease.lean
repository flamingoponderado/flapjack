import Flapjack.Compiler.Backend.ClosKnown.Inline

/-! The following facts justify the recursive inlining decrease for the
fuelled Flapjack implementation. Its option-valued decision function differs
from HOL's total function, so these are not tagged as HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.ClosKnown

theorem inlineFactor_positive_of_letInline (fuel : Nat) (c : Config) (approx : ValApprox)
    (loc : Option Nat) (arity : Nat) (body : ClosLang.Exp)
    (h : decideInlineFuel fuel c approx loc arity = some (.letInline body)) :
    0 < c.inlineFactor := by
  by_cases hz : c.inlineFactor = 0
  · cases loc <;> cases approx <;> simp [decideInlineFuel, hz] at h <;>
      split at h <;> simp_all
  · omega

theorem inlineFactor_decreases_of_letInline (fuel : Nat) (c : Config) (approx : ValApprox)
    (loc : Option Nat) (arity : Nat) (body : ClosLang.Exp)
    (h : decideInlineFuel fuel c approx loc arity = some (.letInline body)) :
    (decInlineFactor c).inlineFactor < c.inlineFactor := by
  have positive := inlineFactor_positive_of_letInline fuel c approx loc arity body h
  simp only [decInlineFactor]
  omega

end Flapjack.Compiler.Backend.ClosKnown
