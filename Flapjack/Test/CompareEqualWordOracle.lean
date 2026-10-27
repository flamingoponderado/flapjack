-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.CompareEqualWordOracle

private def matches0 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (18, 4, (.ite .equal 2 ((.imm 0)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) ((.seq ((.assign 8 ((.load ((.var 4)))))) ((.seq ((.assign 9 ((.load ((.var 6)))))) ((.ite .equal 8 ((.reg 9)) ((.seq ((.assign 2 ((.op .sub [(.var 2), (.const 1)])))) ((.seq ((.assign 4 ((.op .sub [(.var 4), (.const 8)])))) ((.seq ((.assign 6 ((.op .sub [(.var 6), (.const 8)])))) ((.call none ((some 18)) [0, 2, 4, 6] none)))))))) ((.ite .lower 8 ((.reg 9)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2]))))))))))))), 0) =>
      true
  | _ => false

private def matches1 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (19, 3, (.ite .test 2 ((.imm 1)) ((.seq ((.assign 1 ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))))) ((.ite .test 1 ((.imm 16)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))))))) ((.ite .test 4 ((.imm 1)) ((.seq ((.assign 1 ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))))) ((.ite .test 1 ((.imm 16)) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))))))) ((.seq ((.assign 11 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 1 ((.load ((.var 11)))))) ((.seq ((.assign 13 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 3 ((.load ((.var 13)))))) ((.seq ((.assign 6 ((.shift .lsr ((.var 1)) (.const 48))))) ((.seq ((.assign 8 ((.shift .lsr ((.var 3)) (.const 48))))) ((.ite .equal 1 ((.reg 3)) ((.seq ((.assign 2 ((.op .add [(.var 11), (.shift .lsl ((.var 6)) (.const 3))])))) ((.seq ((.assign 4 ((.op .add [(.var 13), (.shift .lsl ((.var 6)) (.const 3))])))) ((.ite .test 1 ((.imm 16)) ((.call none ((some 18)) [0, 6, 2, 4] none)) ((.call none ((some 18)) [0, 6, 4, 2] none)))))))) ((.ite .test 1 ((.imm 16)) ((.ite .test 3 ((.imm 16)) ((.ite .lower 6 ((.reg 8)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))))) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))))) ((.ite .test 3 ((.imm 16)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) ((.ite .lower 6 ((.reg 8)) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2]))))))))))))))))))))))))))), 0) =>
      true
  | _ => false

private def matches2 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (20, 4, (.seq ((.ite .equal 2 ((.imm 0)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 1 ((.load ((.var 4)))))) ((.seq ((.assign 3 ((.load ((.var 6)))))) ((.seq ((.call ((some ([5], (live0, .ln), .skip, 20, 2))) ((some 21)) [1, 3] none)) ((.seq ((.ite .equal 5 ((.imm 1)) .skip ((.return 0 [5])))) ((.seq ((.assign 2 ((.op .sub [(.var 2), (.const 1)])))) ((.seq ((.assign 4 ((.op .add [(.var 4), (.const 8)])))) ((.seq ((.assign 6 ((.op .add [(.var 6), (.const 8)])))) ((.call none ((some 20)) [0, 2, 4, 6] none))))))))))))))))), 0) =>
      decide (live0 = Flapjack.sptListInsert [0, 2, 4, 6] .ln)
  | _ => false

private def matches3 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (21, 3, (.seq ((.ite .equal 2 ((.reg 4)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 1 ((.op .and [(.var 2), (.var 4)])))) ((.seq ((.ite .test 1 ((.imm 1)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 20 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 40 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 21 ((.load ((.var 20)))))) ((.seq ((.assign 41 ((.load ((.var 40)))))) ((.seq ((.ite .test 21 ((.imm 12)) ((.seq ((.assign 1 ((.op .and [(.var 21), (.const 281474976710654)])))) ((.seq ((.ite .equal 1 ((.imm 482)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) .skip)) ((.seq ((.ite .equal 1 ((.imm 498)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) .skip)) ((.seq ((.ite .equal 21 ((.reg 41)) .skip ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))))) ((.seq ((.assign 6 ((.shift .lsr ((.var 21)) (.const 48))))) ((.seq ((.assign 20 ((.op .add [(.var 20), (.const 8)])))) ((.seq ((.assign 40 ((.op .add [(.var 40), (.const 8)])))) ((.call none ((some 20)) [0, 6, 20, 40] none)))))))))))))))) .skip)) ((.seq ((.ite .equal 21 ((.reg 41)) .skip ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))))) ((.seq ((.ite .test 21 ((.imm 4)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 1 ((.op .and [(.var 21), (.const 24)])))) ((.seq ((.ite .equal 1 ((.imm 16)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 6 ((.shift .lsr ((.var 21)) (.const 48))))) ((.seq ((.assign 2 ((.op .add [(.var 20), (.shift .lsl ((.var 6)) (.const 3))])))) ((.seq ((.assign 4 ((.op .add [(.var 40), (.shift .lsl ((.var 6)) (.const 3))])))) ((.call none ((some 18)) [0, 6, 2, 4] none))))))))))))))))))))))))))))))), 0) =>
      true
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0, entry1, entry2, entry3] =>
      matches0 entry0 &&
      matches1 entry1 &&
      matches2 entry2 &&
      matches3 entry3
  | _ => false

end Flapjack.Test.CompareEqualWordOracle
