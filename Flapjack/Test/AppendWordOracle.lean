-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.AppendWordOracle

private def matches0 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (33, 3, (.ite .test 4 ((.imm 1)) ((.return 0 [2])) ((.seq ((.set ((.temp 0)) ((.var 2)))) ((.seq ((.set ((.temp 1)) ((.var 4)))) ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 3 ((.const 562949953421315)))) ((.seq ((.assign 5 ((.op .sub [(.lookup .triggerGC), (.var 1)])))) ((.seq ((.assign 7 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 5)])))) ((.seq ((.set ((.temp 2)) ((.var 7)))) ((.call none ((some 34)) [0, 1, 4, 3, 5, 7] none))))))))))))))))), 0) =>
      true
  | _ => false

private def matches1 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (34, 6, (.seq ((.assign 1 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 3 ((.load ((.op .add [(.var 1), (.const 8)])))))) ((.seq ((.assign 5 ((.load ((.op .add [(.var 1), (.const 16)])))))) ((.seq ((.ite .lower 8 ((.imm 24)) ((.seq ((.assign 1 ((.const 0)))) ((.call none ((some 35)) [0, 4, 1] none)))) .skip)) ((.seq ((.store ((.var 2)) 6)) ((.seq ((.store ((.op .add [(.var 2), (.const 8)])) 3)) ((.seq ((.ite .test 5 ((.imm 1)) .skip ((.seq ((.assign 10 ((.op .add [(.var 10), (.const 768)])))) ((.seq ((.assign 8 ((.op .sub [(.var 8), (.const 24)])))) ((.seq ((.store ((.op .add [(.var 2), (.const 16)])) 10)) ((.seq ((.assign 2 ((.op .add [(.var 2), (.const 24)])))) ((.call none ((some 34)) [0, 2, 5, 6, 8, 10] none)))))))))))) ((.seq ((.assign 1 ((.lookup ((.temp 0)))))) ((.seq ((.assign 3 ((.lookup ((.temp 2)))))) ((.seq ((.store ((.op .add [(.var 2), (.const 16)])) 1)) ((.seq ((.set .nextFree ((.op .add [(.var 2), (.const 24)])))) ((.return 0 [3]))))))))))))))))))))))), 0) =>
      true
  | _ => false

private def matches2 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (35, 3, (.ite .test 2 ((.imm 1)) ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.seq ((.assign 1 ((.op .add [(.var 4), (.shift .lsr ((.var 1)) (.const 1))])))) ((.seq ((.assign 4 ((.lookup ((.temp 0)))))) ((.seq ((.assign 2 ((.lookup ((.temp 1)))))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 2305843009213693951)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live0, live1))) .skip)))) .skip)))))))) ((.call none ((some 33)) [0, 4, 2] none)))))))))))) ((.seq ((.assign 2 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.const 16)])))))) ((.seq ((.assign 4 ((.op .add [(.var 4), (.const 12)])))) ((.call none ((some 35)) [0, 2, 4] none))))))), 0) =>
      decide (live0 = Flapjack.sptListInsert [0] .ln) &&
      decide (live1 = Flapjack.sptListInsert [2, 4] .ln)
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0, entry1, entry2] =>
      matches0 entry0 &&
      matches1 entry1 &&
      matches2 entry2
  | _ => false

end Flapjack.Test.AppendWordOracle
