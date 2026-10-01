import Flapjack.RiscV.WordDeadCode
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

namespace Flapjack

/-- Flapjack-only Option packaging: a pair of successful encodings introduces
no additional failure point. There is no HOL declaration for this helper. -/
private theorem optionPairDomain {α β γ : Type} (first : Option α)
    (second : Option β) (make : α → β → γ) :
    (first.bind fun a => second.bind fun b => some (make a b)).isSome =
      (first.isSome && second.isSome) := by
  cases first <;> cases second <;> rfl

/-- Flapjack-only Option packaging for one successful constructor. -/
private theorem optionMapDomain {α β : Type} (value : Option α) (make : α → β) :
    (value.bind fun a => some (make a)).isSome = value.isSome := by
  cases value <;> rfl

/-- The actual allocator's three-to-two transform preserves precisely the
partial production-to-native codec domain. Its two arithmetic assignment
rewrites introduce only accepted Move/Assign nodes. Every recursive constructor
is covered, including the handler of a nonreturning Call, which the actual
production function traverses. Five-register AddCarry rejection is retained.

This is Flapjack carrier infrastructure, with no corresponding HOL theorem:
it proves a property of the executed production transform, not equality with
HOL's three-to-two pass or compiler correctness. No output-codec success,
source-image, memory guard, pass-success or evaluation premise is assumed. -/
theorem wordLangProgToHOL_wordThreeToTwoReg_isSome {width : Nat}
    (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (RiscV.wordThreeToTwoReg program)).isSome =
      (wordLangProgToHOL program).isSome := by
  fun_induction RiscV.wordThreeToTwoReg program <;>
    simp_all [wordLangProgToHOL, optionPairDomain, optionMapDomain]

end Flapjack
