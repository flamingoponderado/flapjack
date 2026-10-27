-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.EmptyCakeWordOracle

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [(64, 0, (.seq ((.assign 2 ((.const 0)))) ((.seq ((.assign 4 ((.const 12)))) ((.seq ((.seq ((.ite .test 4 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live0, .ln))))))) ((.seq ((.move 0 [(1, 4)])) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live1, live2))) .skip)))) .skip)))))))) ((.mustTerminate ((.call ((some ([6], (live3, .ln), .skip, 64, 2))) ((some 10)) [4, 2] none)))))))))) ((.seq ((.assign 8 ((.const 4)))) ((.seq ((.assign 10 ((.const 0)))) ((.seq ((.seq ((.store ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 10)) (.const 1))])])) 8)) ((.assign 12 (.const 2))))) ((.seq ((.seq ((.set .globals ((.var 6)))) ((.seq ((.set .globReal ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))])))) ((.assign 14 (.const 2))))))) ((.seq ((.call ((some ([18], (live4, .ln), .skip, 64, 3))) ((some 76)) [] ((some (16, (.move 0 [(18, 16)]), 64, 4))))) ((.return 0 [18]))))))))))))))))), 5), (76, 0, (.seq ((.assign 2 ((.const 4)))) ((.seq ((.call ((some ([4], (live5, .ln), .skip, 76, 2))) ((some 62)) [2] none)) ((.seq ((.assign 6 (.const 2))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 16)])) 6)) ((.assign 8 (.const 2))))) ((.call none ((some 80)) [0] none))))))))), 3), (80, 0, (.seq ((.assign 2 ((.const 4)))) ((.seq ((.call ((some ([4], (live6, .ln), .skip, 80, 2))) ((some 62)) [2] none)) ((.seq ((.assign 6 (.const 2))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 24)])) 6)) ((.assign 8 (.const 2))))) ((.call none ((some 84)) [0] none))))))))), 3), (84, 0, (.seq ((.call ((some ([2], (live7, .ln), .skip, 84, 2))) ((some 73)) [] none)) ((.seq ((.assign 4 (.const 2))) ((.call none ((some 88)) [0] none))))), 3), (73, 0, (.return 0 [2]), 2), (88, 0, (.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 16)) ((.seq .skip ((.seq ((.assign 1 ((.const 16)))) ((.seq ((.alloc 1 (live8, .ln))) .skip)))))) .skip)))) ((.seq ((.assign 2 (.const 2))) ((.seq ((.seq ((.set .triggerGC ((.op .sub [(.lookup .triggerGC), (.const 16)])))) ((.seq ((.assign 1 ((.op .sub [(.lookup .endOfHeap), (.const 16)])))) ((.seq ((.set .endOfHeap ((.var 1)))) ((.seq ((.assign 3 ((.const 281474976710667)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 2)) .skip)))) ((.assign 4 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 1)])))))))))))))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 32)])) 4)) ((.assign 6 (.const 2))))) ((.return 0 [6]))))))))), 2)] =>
      decide (live0 = Flapjack.sptListInsert [0] .ln) &&
      decide (live1 = Flapjack.sptListInsert [0] .ln) &&
      decide (live2 = Flapjack.sptListInsert [2, 4] .ln) &&
      decide (live3 = Flapjack.sptListInsert [0] .ln) &&
      decide (live4 = Flapjack.sptListInsert [0] .ln) &&
      decide (live5 = Flapjack.sptListInsert [0] .ln) &&
      decide (live6 = Flapjack.sptListInsert [0] .ln) &&
      decide (live7 = Flapjack.sptListInsert [0] .ln) &&
      decide (live8 = Flapjack.sptListInsert [0] .ln)
  | _ => false

end Flapjack.Test.EmptyCakeWordOracle
