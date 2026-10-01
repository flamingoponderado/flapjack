import Flapjack.RiscV.WordDeadCode
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

namespace Flapjack

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
    simp_all [wordLangProgToHOL, WordProgCarrierCodec.optionPairDomain,
      WordProgCarrierCodec.optionMapDomain]

end Flapjack
