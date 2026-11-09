module

public import Flapjack.Compiler.Backend.ClosKnown.Inline

@[expose] public section

/-! The following facts justify the recursive inlining decrease for the
checked Flapjack implementation. The option-valued wrappers are infrastructure. -/
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

end Flapjack.Compiler.Backend.ClosKnown
