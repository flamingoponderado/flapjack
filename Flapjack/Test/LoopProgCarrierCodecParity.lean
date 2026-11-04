import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec

/-!
# Width-specialized Loop program codec fixtures

These fixtures check structural conversion at the exact loop_to_word source
boundary. They are carrier tests, not original Pancake execution parity and do
not claim production compiler routing.
-/

namespace Flapjack.Test.LoopProgCarrierCodecParity

open Flapjack Flapjack.Basis.Pure.MlString Flapjack.LoopToWord

private def exactNested : HolLoopProg 8 :=
  .seq
    (.loop .ln
      (.ite .equal 1 (.reg 2)
        (.ffi (ofString "putchar") 3 4 5 6 .ln)
        (.tick) .ln)
      .ln)
    (.call (some ([7], .ln)) (some 12) [8]
      (some (9, .skip, .return [7], .ln)))

private def exactNestedExecutable : LoopProg (BitVec 8) :=
  holLoopProgToExecutableCanonical exactNested

example : loopProgExecRel exactNestedExecutable exactNested :=
  holLoopProgToExecutableCanonical_rel exactNested

private def exactExpressionRejected : LoopProg (BitVec 8) :=
  .assign 3 (.cmp .equal (.var 1) (.const 0))

private def byteNameFfi : LoopProg (BitVec 8) :=
  .ffi "write" 1 2 3 4 []

example : sptLookup 2 (Flapjack.LoopToWord.toNumSetHOL [2, 2]) = some () := by
  exact (sptLookup_toNumSetHOL_iff_mem 2 [2, 2]).2 (by simp)

end Flapjack.Test.LoopProgCarrierCodecParity
