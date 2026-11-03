import Flapjack.Compiler.Backend.ClosKnown.Inline

/-! The following facts justify the recursive inlining decrease for the
checked Flapjack implementation. The option-valued wrappers are infrastructure;
the corresponding total source theorem is in `Inline.DecisionCorrect`. -/
namespace Flapjack.Compiler.Backend.ClosKnown

/-- An inlining decision containing a body requires a positive factor. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "decide_inline_LetInline"]
theorem decideInlineLetInline {L : Type} (c : Config) (approx : ValApprox) (loc : Option L)
    (arity : Nat) (body : ClosLang.Exp)
    (h : decideInlineHOL c approx loc arity = .letInline body) : 0 < c.inlineFactor := by
  by_cases zero : c.inlineFactor = 0
  · cases loc <;> cases approx <;> simp [decideInlineHOL, zero] at h <;>
      split at h <;> simp_all
  · omega

theorem inlineFactor_positive_of_letInline (fuel : Nat) (c : Config) (approx : ValApprox)
    (loc : Option Nat) (arity : Nat) (body : ClosLang.Exp)
    (h : decideInlineFuel fuel c approx loc arity = some (.letInline body)) :
    0 < c.inlineFactor := by
  by_cases hz : c.inlineFactor = 0
  · cases loc <;> cases approx <;> simp [decideInlineFuel, decideInlineHOL, hz] at h <;>
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
