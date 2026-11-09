-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.MtiOpsWordOracle

private def matches0 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (0, 0, (.seq ((.assign 1 ((.var 4)))) ((.seq ((.ite .test 4 ((.imm 1)) .skip ((.assign 1 ((.op .and [(.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]))), (.const 281474976710654)])))))) ((.ite .equal 1 ((.imm 482)) ((.assign 8 (.const 18))) ((.assign 8 (.const 2)))))))), 2) =>
      true
  | _ => false

private def matches1 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (1, 0, (.seq ((.assign 1 ((.shift .lsr ((.var 4)) (.const 1))))) ((.seq ((.inst ((.arith ((.longMul 3 1 1 6)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.op .and [(.const 1), (.op .or [(.var 4), (.var 6)])])])))) ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 1))))) ((.seq ((.ite .equal 3 ((.imm 0)) .skip ((.mustTerminate ((.call ((some ([1], (live0, .ln), .skip, 5, 2))) ((some 15)) [4, 6] none)))))) ((.move 2 [(8, 1)]))))))))))), 3) =>
      decide (live0 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches2 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (2, 0, (.seq ((.assign 1 ((.op .or [(.var 4), (.var 6)])))) ((.seq ((.assign 1 ((.op .or [(.var 1), (.shift .lsr ((.var 1)) (.const 63))])))) ((.ite .test 1 ((.imm 1)) ((.seq ((.assign 1 ((.const 0)))) ((.seq ((.mustTerminate ((.call ((some ([1], (live1, .ln), .skip, 5, 3))) ((some 23)) [1, 4, 6] none)))) ((.assign 8 ((.shift .lsl ((.var 1)) (.const 2))))))))) ((.seq ((.mustTerminate ((.call ((some ([1], (live2, .ln), .skip, 5, 2))) ((some 16)) [4, 6] none)))) ((.move 2 [(8, 1)]))))))))), 4) =>
      decide (live1 = Flapjack.sptListInsert [0] .ln) &&
      decide (live2 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches3 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (3, 0, (.seq ((.assign 1 ((.op .or [(.var 4), (.var 6)])))) ((.seq ((.assign 1 ((.op .or [(.var 1), (.shift .lsr ((.var 1)) (.const 63))])))) ((.ite .test 1 ((.imm 1)) ((.seq ((.inst ((.arith ((.div 1 4 6)))))) ((.assign 8 ((.shift .lsl ((.var 1)) (.const 2))))))) ((.seq ((.mustTerminate ((.call ((some ([1], (live3, .ln), .skip, 5, 2))) ((some 16)) [4, 6] none)))) ((.move 2 [(8, 1)]))))))))), 4) =>
      decide (live3 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches4 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (4, 0, (.seq ((.assign 1 ((.op .or [(.var 4), (.var 6)])))) ((.seq ((.assign 1 ((.op .or [(.var 1), (.shift .lsr ((.var 1)) (.const 63))])))) ((.ite .test 1 ((.imm 1)) ((.seq ((.assign 1 ((.const 0)))) ((.seq ((.inst ((.arith ((.longDiv 1 3 1 4 6)))))) ((.assign 8 ((.shift .lsl ((.var 1)) (.const 2))))))))) ((.seq ((.mustTerminate ((.call ((some ([1], (live4, .ln), .skip, 5, 2))) ((some 16)) [4, 6] none)))) ((.move 2 [(8, 1)]))))))))), 4) =>
      decide (live4 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches5 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (5, 0, (.seq ((.ite .test 10 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live5, .ln))))))) ((.seq ((.assign 1 ((.var 10)))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live6, live7))) .skip)))) .skip)))))))) ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 5 ((.op .or [(.shift .lsl ((.var 10)) (.const 46)), (.const 19)])))) ((.seq ((.assign 7 ((.shift .lsr ((.var 10)) (.const 2))))) ((.seq ((.assign 9 ((.const 1)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 5)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 12)) .skip)))) ((.seq ((.seq ((.assign 3 ((.op .or [(.const 1), (.shift .lsl ((.op .sub [(.lookup .nextFree), (.lookup .currHeap)])) (.const 5))])))) ((.seq ((.ite .lower 9 ((.imm 1)) ((.assign 3 ((.op .or [(.var 3), (.shift .lsl ((.var 9)) (.const 3))])))) ((.assign 3 ((.op .or [(.var 3), (.const 8)])))))) ((.ite .lower 7 ((.imm 3)) ((.assign 3 ((.op .or [(.var 3), (.shift .lsl ((.var 7)) (.const 1))])))) ((.assign 3 ((.op .or [(.var 3), (.const 6)])))))))))) ((.seq ((.set .nextFree ((.op .add [(.var 1), (.const 8), (.shift .lsl ((.var 7)) (.const 3))])))) ((.seq ((.assign 15 ((.var 8)))) ((.seq ((.assign 13 ((.op .add [(.var 1), (.const 16)])))) ((.seq ((.assign 11 ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 8), (.shift .lsl ((.var 6)) (.const 1))])))) ((.ite .test 15 ((.reg 15)) ((.assign 8 ((.var 3)))) ((.mustTerminate ((.call ((some ([8], (live8, .ln), .skip, 5, 2))) ((some 24)) [15, 11, 13, 3] none))))))))))))))))))))))))))))))), 3) =>
      decide (live5 = Flapjack.sptListInsert [0] .ln) &&
      decide (live6 = Flapjack.sptListInsert [0] .ln) &&
      decide (live7 = Flapjack.sptListInsert [4, 6, 8, 10, 12] .ln) &&
      decide (live8 = Flapjack.sptListInsert [0] .ln)
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0, entry1, entry2, entry3, entry4, entry5] =>
      matches0 entry0 &&
      matches1 entry1 &&
      matches2 entry2 &&
      matches3 entry3 &&
      matches4 entry4 &&
      matches5 entry5
  | _ => false

end Flapjack.Test.MtiOpsWordOracle
