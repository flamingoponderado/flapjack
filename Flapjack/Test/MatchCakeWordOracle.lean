-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.MatchCakeWordOracle

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [(92, 0, (.seq ((.assign 2 ((.const 4)))) ((.seq ((.assign 4 ((.const 4)))) ((.seq ((.seq ((.assign 1 ((.var 2)))) ((.seq ((.assign 3 ((.var 4)))) ((.seq ((.assign 5 ((.op .and [(.var 1), (.var 3)])))) ((.seq ((.ite .test 5 ((.imm 1)) .skip ((.ite .equal 1 ((.reg 3)) .skip ((.seq ((.mustTerminate ((.call ((some ([1], (live0, .ln), .skip, 92, 2))) ((some 21)) [1, 3] none)))) ((.assign 3 ((.const 1)))))))))) ((.ite .equal 1 ((.reg 3)) ((.assign 6 (.const 18))) ((.assign 6 (.const 2))))))))))))) ((.seq ((.ite .equal 6 ((.imm 18)) ((.seq ((.assign 8 ((.const 8)))) ((.move 0 [(12, 8)])))) ((.seq ((.assign 10 ((.const 12)))) ((.move 0 [(12, 10)])))))) ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 16)) ((.seq .skip ((.seq ((.assign 1 ((.const 16)))) ((.seq ((.alloc 1 (live1, live2))) .skip)))))) .skip)))) ((.seq ((.seq ((.set .triggerGC ((.op .sub [(.lookup .triggerGC), (.const 16)])))) ((.seq ((.assign 1 ((.op .sub [(.lookup .endOfHeap), (.const 16)])))) ((.seq ((.set .endOfHeap ((.var 1)))) ((.seq ((.assign 3 ((.const 281474976710667)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 12)) .skip)))) ((.assign 14 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 1)])))))))))))))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 40)])) 14)) ((.assign 18 (.const 2))))) ((.return 0 [18]))))))))))))))), 3)] =>
      decide (live0 = Flapjack.sptListInsert [0] .ln) &&
      decide (live1 = Flapjack.sptListInsert [0] .ln) &&
      decide (live2 = Flapjack.sptListInsert [12] .ln)
  | _ => false

end Flapjack.Test.MatchCakeWordOracle
