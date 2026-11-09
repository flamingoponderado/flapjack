-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.TmcProgramWordOracle

private def matches0 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (3, 2, (.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 24)) ((.seq .skip ((.seq ((.assign 1 ((.const 24)))) ((.seq ((.alloc 1 (live0, live1))) .skip)))))) .skip)))) ((.seq ((.assign 4 ((.const 0)))) ((.seq ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 3 ((.const 562949953421315)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 4)) ((.seq ((.store ((.op .add [(.var 1), (.const 16)])) 2)) .skip)))))) ((.seq ((.assign 6 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 5)])))) ((.set .nextFree ((.op .add [(.var 1), (.const 24)])))))))))))) ((.seq ((.assign 8 ((.const 0)))) ((.seq ((.call ((some ([10], (live2, live3), .skip, 3, 2))) ((some 59)) [2, 6, 8] none)) ((.seq ((.assign 12 ((.var 6)))) ((.return 0 [12]))))))))))))), 0) =>
      decide (live0 = Flapjack.sptListInsert [0] .ln) &&
      decide (live1 = Flapjack.sptListInsert [2] .ln) &&
      decide (live2 = Flapjack.sptListInsert [0] .ln) &&
      decide (live3 = Flapjack.sptListInsert [6] .ln)
  | _ => false

private def matches1 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (59, 4, (.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 24)) ((.seq .skip ((.seq ((.assign 1 ((.const 24)))) ((.seq ((.alloc 1 (live4, live5))) .skip)))))) .skip)))) ((.seq ((.assign 8 ((.const 0)))) ((.seq ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 3 ((.const 562949953421315)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 8)) ((.seq ((.store ((.op .add [(.var 1), (.const 16)])) 2)) .skip)))))) ((.seq ((.assign 10 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 5)])))) ((.set .nextFree ((.op .add [(.var 1), (.const 24)])))))))))))) ((.seq ((.seq ((.store ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 6)) (.const 1))])])) 10)) ((.assign 12 (.const 2))))) ((.seq ((.assign 14 ((.const 0)))) ((.call none ((some 59)) [0, 2, 10, 14] none))))))))))), 0) =>
      decide (live4 = Flapjack.sptListInsert [0] .ln) &&
      decide (live5 = Flapjack.sptListInsert [2, 4, 6] .ln)
  | _ => false

private def matches2 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (7, 1, (.return 0 [2]), 0) =>
      true
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0, entry1, entry2] =>
      matches0 entry0 &&
      matches1 entry1 &&
      matches2 entry2
  | _ => false

end Flapjack.Test.TmcProgramWordOracle
