-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.RefByte64WordOracle

private def matches0 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (9, 4, (.seq ((.ite .test 2 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live0, .ln))))))) ((.seq ((.assign 1 ((.shift .lsr ((.op .add [(.shift .lsr ((.var 2)) (.const 2)), (.const 8)])) (.const 1))))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live1, live2))) .skip)))) .skip)))))))) ((.seq ((.assign 5 ((.shift .lsr ((.op .add [(.shift .lsr ((.var 2)) (.const 2)), (.const 8)])) (.const 3))))) ((.seq ((.assign 7 ((.shift .lsl ((.var 5)) (.const 2))))) ((.seq ((.assign 9 ((.lookup .nextFree)))) ((.seq ((.assign 1 ((.op .add [(.var 9), (.shift .lsl ((.var 5)) (.const 3))])))) ((.seq ((.set .nextFree ((.op .add [(.var 1), (.const 8)])))) ((.seq ((.assign 3 ((.op .or [(.shift .lsl ((.op .sub [(.var 9), (.lookup .currHeap)])) (.const 5)), (.const 1)])))) ((.seq ((.assign 5 ((.op .or [(.op .or [(.shift .lsl ((.op .add [(.shift .lsr ((.var 2)) (.const 2)), (.const 8)])) (.const 45)), (.const 7)]), (.var 6)])))) ((.seq ((.seq ((.assign 4 ((.shift .lsr ((.var 4)) (.const 2))))) ((.seq ((.assign 4 ((.op .or [(.var 4), (.shift .lsl ((.var 4)) (.const 8))])))) ((.seq ((.assign 4 ((.op .or [(.var 4), (.shift .lsl ((.var 4)) (.const 16))])))) ((.assign 4 ((.op .or [(.var 4), (.shift .lsl ((.var 4)) (.const 32))])))))))))) ((.seq ((.store ((.var 9)) 5)) ((.seq ((.assign 11 ((.op .and [(.shift .lsr ((.var 2)) (.const 2)), (.const 7)])))) ((.seq ((.assign 13 ((.const 0)))) ((.seq ((.store ((.var 1)) 13)) ((.seq ((.ite .equal 11 ((.imm 0)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 0)))))) ((.ite .equal 11 ((.imm 1)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 1)))))) ((.ite .equal 11 ((.imm 2)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 2)))))) ((.ite .equal 11 ((.imm 3)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 3)))))) ((.ite .equal 11 ((.imm 4)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 4)))))) ((.ite .equal 11 ((.imm 5)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 5)))))) ((.ite .equal 11 ((.imm 6)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 6)))))) ((.ite .equal 11 ((.imm 7)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 7)))))) .skip)))))))))))))))))))))))))))))))) ((.seq ((.assign 7 ((.op .sub [(.var 7), (.const 4)])))) ((.call none ((some 11)) [0, 9, 4, 7, 3] none))))))))))))))))))))))))))))))))))), 0) =>
      decide (live0 = Flapjack.sptListInsert [0] .ln) &&
      decide (live1 = Flapjack.sptListInsert [0] .ln) &&
      decide (live2 = Flapjack.sptListInsert [2, 4, 6] .ln)
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0] =>
      matches0 entry0
  | _ => false

end Flapjack.Test.RefByte64WordOracle
