-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.LongDivWordOracle

private def matches0 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (22, 7, (.ite .test 2 ((.reg 2)) ((.seq ((.set ((.temp 28)) ((.var 10)))) ((.return 0 [8])))) ((.seq ((.assign 6 ((.op .or [(.shift .lsr ((.var 6)) (.const 1)), (.shift .lsl ((.var 4)) (.const 63))])))) ((.seq ((.assign 4 ((.shift .lsr ((.var 4)) (.const 1))))) ((.seq ((.assign 8 ((.shift .lsl ((.var 8)) (.const 1))))) ((.seq ((.assign 2 ((.op .sub [(.var 2), (.const 1)])))) ((.seq ((.ite .lower 12 ((.reg 4)) ((.call none ((some 22)) [0, 2, 4, 6, 8, 10, 12] none)) .skip)) ((.seq ((.ite .equal 12 ((.reg 4)) ((.ite .lower 10 ((.reg 6)) ((.call none ((some 22)) [0, 2, 4, 6, 8, 10, 12] none)) .skip)) .skip)) ((.seq ((.assign 8 ((.op .add [(.var 8), (.const 1)])))) ((.seq ((.assign 16 ((.op .xor [(.var 6), (.const 18446744073709551615)])))) ((.seq ((.assign 14 ((.op .xor [(.var 4), (.const 18446744073709551615)])))) ((.seq ((.assign 1 ((.const 1)))) ((.seq ((.inst ((.arith ((.addCarry 10 10 16 1)))))) ((.seq ((.inst ((.arith ((.addCarry 12 12 14 1)))))) ((.call none ((some 22)) [0, 2, 4, 6, 8, 10, 12] none))))))))))))))))))))))))))), 0) =>
      true
  | _ => false

private def matches1 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (23, 4, (.seq ((.assign 10 ((.const 0)))) ((.seq ((.assign 11 ((.const 64)))) ((.call none ((some 22)) [0, 11, 6, 10, 10, 4, 2] none))))), 0) =>
      true
  | _ => false

private def matches2 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (22, 7, .skip, 0) =>
      true
  | _ => false

private def matches3 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (23, 4, (.seq ((.inst ((.arith ((.longDiv 1 3 2 4 6)))))) ((.seq ((.set ((.temp 28)) ((.var 3)))) ((.return 0 [1]))))), 0) =>
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

end Flapjack.Test.LongDivWordOracle
