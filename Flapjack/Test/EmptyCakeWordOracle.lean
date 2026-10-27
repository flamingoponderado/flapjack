-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.EmptyCakeWordOracle

/-- Match the complete captured entry function, including every live set. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [(64, 0, (.seq ((.assign 2 ((.const 0)))) ((.seq ((.assign 4 ((.const 12)))) ((.seq ((.seq ((.ite .test 4 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const (word0))))) ((.alloc 1 (live0, .ln))))))) ((.seq ((.move 0 [(1, 4)])) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const (word1))))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live1, live2))) .skip)))) .skip)))))))) ((.mustTerminate ((.call ((some ([6], (live3, .ln), .skip, 64, 2))) ((some 10)) [4, 2] none)))))))))) ((.seq ((.assign 8 ((.const 4)))) ((.seq ((.assign 10 ((.const 0)))) ((.seq ((.seq ((.store ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 10)) (.const 1))])])) 8)) ((.assign 12 (.const 2))))) ((.seq ((.seq ((.set .globals ((.var 6)))) ((.seq ((.set .globReal ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))])))) ((.assign 14 (.const 2))))))) ((.seq ((.call ((some ([18], (live4, .ln), .skip, 64, 3))) ((some 76)) [] ((some (16, (.move 0 [(18, 16)]), 64, 4))))) ((.return 0 [18]))))))))))))))))), 5)] =>
      decide (live0 = Flapjack.sptListInsert [0] .ln) &&
      decide (live1 = Flapjack.sptListInsert [0] .ln) &&
      decide (live2 = Flapjack.sptListInsert [2, 4] .ln) &&
      decide (live3 = Flapjack.sptListInsert [0] .ln) &&
      decide (live4 = Flapjack.sptListInsert [0] .ln) &&
      word0 == (-1 : BitVec 64) &&
      word1 == (-1 : BitVec 64)
  | _ => false

end Flapjack.Test.EmptyCakeWordOracle
