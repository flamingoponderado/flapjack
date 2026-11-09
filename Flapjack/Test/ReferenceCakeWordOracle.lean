-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.ReferenceCakeWordOracle

private def matches0 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (62, 1, (.seq ((.assign 4 ((.lookup .globals)))) ((.seq ((.assign 6 ((.const 0)))) ((.seq ((.assign 8 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 6)) (.const 1))])])))))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 2 8 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 2), (.var 8)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live0, live1), .skip, 62, 2))) ((some 13)) [2, 8] none)))))) ((.move 2 [(10, 1)])))))))) ((.seq ((.assign 12 ((.shift .lsl ((.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) (.const 48))) (.const 2))))) ((.seq ((.assign 14 ((.const 0)))) ((.seq ((.seq ((.store ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 14)) (.const 1))])])) 10)) ((.assign 16 (.const 2))))) ((.seq ((.seq ((.assign 1 ((.var 10)))) ((.seq ((.assign 3 ((.var 12)))) ((.seq ((.assign 5 ((.op .or [(.var 1), (.var 3)])))) ((.seq ((.ite .test 5 ((.imm 1)) .skip ((.seq ((.mustTerminate ((.call ((some ([1], (live2, live3), .skip, 62, 3))) ((some 19)) [1, 3] none)))) ((.assign 3 ((.const 1)))))))) ((.ite .less 1 ((.reg 3)) ((.assign 18 (.const 18))) ((.assign 18 (.const 2))))))))))))) ((.ite .equal 18 ((.imm 18)) ((.return 0 [16])) ((.seq ((.assign 22 ((.const 0)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 10 10 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 10), (.var 10)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live4, live5), .skip, 62, 4))) ((some 13)) [10, 10] none)))))) ((.move 2 [(24, 1)])))))))) ((.seq ((.seq ((.ite .test 24 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live6, .ln))))))) ((.seq ((.move 0 [(1, 24)])) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live7, live8))) .skip)))) .skip)))))))) ((.mustTerminate ((.call ((some ([26], (live9, live10), .skip, 62, 5))) ((some 10)) [24, 22] none)))))))))) ((.seq ((.seq ((.set .globals ((.var 26)))) ((.seq ((.set .globReal ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 26)) (.const 5))])))) ((.assign 28 (.const 2))))))) ((.seq ((.assign 30 ((.const 4)))) ((.seq ((.seq ((.inst ((.arith ((.subOverflow 1 12 30 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 12), (.var 30)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live11, live12), .skip, 62, 6))) ((some 14)) [12, 30] none)))))) ((.move 2 [(32, 1)])))))))) ((.call none ((some 63)) [0, 26, 4, 32] none))))))))))))))))))))))))))))))), 7) =>
      decide (live0 = Flapjack.sptListInsert [0] .ln) &&
      decide (live1 = Flapjack.sptListInsert [4] .ln) &&
      decide (live2 = Flapjack.sptListInsert [0] .ln) &&
      decide (live3 = Flapjack.sptListInsert [4, 10, 12, 16] .ln) &&
      decide (live4 = Flapjack.sptListInsert [0] .ln) &&
      decide (live5 = Flapjack.sptListInsert [4, 12, 22] .ln) &&
      decide (live6 = Flapjack.sptListInsert [0] .ln) &&
      decide (live7 = Flapjack.sptListInsert [0] .ln) &&
      decide (live8 = Flapjack.sptListInsert [4, 12, 22, 24] .ln) &&
      decide (live9 = Flapjack.sptListInsert [0] .ln) &&
      decide (live10 = Flapjack.sptListInsert [4, 12] .ln) &&
      decide (live11 = Flapjack.sptListInsert [0] .ln) &&
      decide (live12 = Flapjack.sptListInsert [4, 26] .ln)
  | _ => false

private def matches1 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (63, 3, (.seq ((.assign 8 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 6)) (.const 1))])])))))) ((.seq ((.seq ((.store ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 6)) (.const 1))])])) 8)) ((.assign 10 (.const 2))))) ((.seq ((.assign 12 ((.const 0)))) ((.seq ((.seq ((.assign 1 ((.var 6)))) ((.seq ((.assign 3 ((.var 12)))) ((.seq ((.assign 5 ((.op .and [(.var 1), (.var 3)])))) ((.seq ((.ite .test 5 ((.imm 1)) .skip ((.ite .equal 1 ((.reg 3)) .skip ((.seq ((.mustTerminate ((.call ((some ([1], (live13, live14), .skip, 63, 2))) ((some 21)) [1, 3] none)))) ((.assign 3 ((.const 1)))))))))) ((.ite .equal 1 ((.reg 3)) ((.assign 14 (.const 18))) ((.assign 14 (.const 2))))))))))))) ((.ite .equal 14 ((.imm 18)) ((.return 0 [10])) ((.seq ((.assign 18 ((.const 4)))) ((.seq ((.seq ((.inst ((.arith ((.subOverflow 1 6 18 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 6), (.var 18)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live15, live16), .skip, 63, 3))) ((some 14)) [6, 18] none)))))) ((.move 2 [(20, 1)])))))))) ((.call none ((some 63)) [0, 2, 4, 20] none))))))))))))))), 4) =>
      decide (live13 = Flapjack.sptListInsert [0] .ln) &&
      decide (live14 = Flapjack.sptListInsert [2, 4, 6, 10] .ln) &&
      decide (live15 = Flapjack.sptListInsert [0] .ln) &&
      decide (live16 = Flapjack.sptListInsert [2, 4] .ln)
  | _ => false

private def matches2 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (64, 0, (.seq ((.assign 2 ((.const 0)))) ((.seq ((.assign 4 ((.const 12)))) ((.seq ((.seq ((.ite .test 4 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live17, .ln))))))) ((.seq ((.move 0 [(1, 4)])) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live18, live19))) .skip)))) .skip)))))))) ((.mustTerminate ((.call ((some ([6], (live20, .ln), .skip, 64, 2))) ((some 10)) [4, 2] none)))))))))) ((.seq ((.assign 8 ((.const 4)))) ((.seq ((.assign 10 ((.const 0)))) ((.seq ((.seq ((.store ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 10)) (.const 1))])])) 8)) ((.assign 12 (.const 2))))) ((.seq ((.seq ((.set .globals ((.var 6)))) ((.seq ((.set .globReal ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))])))) ((.assign 14 (.const 2))))))) ((.seq ((.call ((some ([18], (live21, .ln), .skip, 64, 3))) ((some 76)) [] ((some (16, (.move 0 [(18, 16)]), 64, 4))))) ((.return 0 [18]))))))))))))))))), 5) =>
      decide (live17 = Flapjack.sptListInsert [0] .ln) &&
      decide (live18 = Flapjack.sptListInsert [0] .ln) &&
      decide (live19 = Flapjack.sptListInsert [2, 4] .ln) &&
      decide (live20 = Flapjack.sptListInsert [0] .ln) &&
      decide (live21 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches3 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (65, 2, (.seq ((.ite .equal 2 ((.imm 2)) ((.assign 6 (.const 18))) ((.assign 6 (.const 2))))) ((.ite .equal 6 ((.imm 18)) ((.return 0 [4])) ((.seq ((.assign 10 ((.const 4)))) ((.seq ((.assign 12 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 10)) (.const 1))])])))))) ((.seq ((.assign 14 ((.const 4)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 14 4 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 14), (.var 4)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live22, live23), .skip, 65, 2))) ((some 13)) [14, 4] none)))))) ((.move 2 [(16, 1)])))))))) ((.call none ((some 65)) [0, 12, 16] none))))))))))))), 3) =>
      decide (live22 = Flapjack.sptListInsert [0] .ln) &&
      decide (live23 = Flapjack.sptListInsert [12] .ln)
  | _ => false

private def matches4 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (66, 3, (.seq ((.ite .equal 2 ((.imm 2)) ((.assign 8 (.const 18))) ((.assign 8 (.const 2))))) ((.ite .equal 8 ((.imm 18)) ((.return 0 [6])) ((.seq ((.assign 12 ((.const 0)))) ((.seq ((.assign 14 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 12)) (.const 1))])])))))) ((.seq ((.seq ((.assign 1 ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.op .add [(.const 8), (.shift .lsr ((.var 4)) (.const 2))])])))) ((.seq ((.assign 3 ((.shift .lsr ((.var 14)) (.const 2))))) ((.seq ((.inst ((.mem .store8 3 ((.addr 1 0)))))) ((.assign 16 (.const 2))))))))) ((.seq ((.assign 18 ((.const 4)))) ((.seq ((.assign 20 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 18)) (.const 1))])])))))) ((.seq ((.assign 22 ((.const 4)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 22 4 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 22), (.var 4)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live24, live25), .skip, 66, 2))) ((some 13)) [22, 4] none)))))) ((.move 2 [(24, 1)])))))))) ((.call none ((some 66)) [0, 20, 24, 6] none))))))))))))))))))), 3) =>
      decide (live24 = Flapjack.sptListInsert [0] .ln) &&
      decide (live25 = Flapjack.sptListInsert [6, 20] .ln)
  | _ => false

private def matches5 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (67, 3, (.seq ((.ite .equal 4 ((.imm 0)) ((.assign 8 (.const 18))) ((.assign 8 (.const 2))))) ((.ite .equal 8 ((.imm 18)) ((.return 0 [2])) ((.seq ((.assign 12 ((.const 4)))) ((.seq ((.seq ((.inst ((.arith ((.subOverflow 1 4 12 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 4), (.var 12)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live26, live27), .skip, 67, 2))) ((some 14)) [4, 12] none)))))) ((.move 2 [(14, 1)])))))))) ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 24)) ((.seq .skip ((.seq ((.assign 1 ((.const 24)))) ((.seq ((.alloc 1 (live28, live29))) .skip)))))) .skip)))) ((.seq ((.seq ((.assign 1 ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.op .add [(.const 8), (.shift .lsr ((.var 14)) (.const 2))])])))) ((.seq ((.inst ((.mem .load8 3 ((.addr 1 0)))))) ((.assign 16 ((.shift .lsl ((.var 3)) (.const 2))))))))) ((.seq ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 3 ((.const 562949953421315)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 16)) ((.seq ((.store ((.op .add [(.var 1), (.const 16)])) 2)) .skip)))))) ((.seq ((.assign 18 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 5)])))) ((.set .nextFree ((.op .add [(.var 1), (.const 24)])))))))))))) ((.call none ((some 67)) [0, 18, 14, 6] none))))))))))))))), 3) =>
      decide (live26 = Flapjack.sptListInsert [0] .ln) &&
      decide (live27 = Flapjack.sptListInsert [2, 6] .ln) &&
      decide (live28 = Flapjack.sptListInsert [0] .ln) &&
      decide (live29 = Flapjack.sptListInsert [2, 6, 14] .ln)
  | _ => false

private def matches6 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (68, 2, (.seq ((.ite .equal 2 ((.imm 2)) ((.assign 6 (.const 18))) ((.assign 6 (.const 2))))) ((.ite .equal 6 ((.imm 18)) ((.return 0 [4])) ((.seq ((.assign 10 ((.const 4)))) ((.seq ((.assign 12 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 10)) (.const 1))])])))))) ((.seq ((.assign 14 ((.const 0)))) ((.seq ((.assign 16 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 14)) (.const 1))])])))))) ((.seq ((.assign 18 ((.shift .lsl ((.op .sub [(.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 16)) (.const 5))])))) (.const 45)), (.const 8)])) (.const 2))))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 18 4 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 18), (.var 4)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live30, live31), .skip, 68, 2))) ((some 13)) [18, 4] none)))))) ((.move 2 [(20, 1)])))))))) ((.call none ((some 68)) [0, 12, 20] none))))))))))))))))), 3) =>
      decide (live30 = Flapjack.sptListInsert [0] .ln) &&
      decide (live31 = Flapjack.sptListInsert [12] .ln)
  | _ => false

private def matches7 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (69, 3, (.seq ((.ite .equal 2 ((.imm 2)) ((.assign 8 (.const 18))) ((.assign 8 (.const 2))))) ((.ite .equal 8 ((.imm 18)) ((.return 0 [6])) ((.seq ((.assign 12 ((.const 0)))) ((.seq ((.assign 14 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 12)) (.const 1))])])))))) ((.seq ((.assign 16 ((.shift .lsl ((.op .sub [(.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 14)) (.const 5))])))) (.const 45)), (.const 8)])) (.const 2))))) ((.seq ((.assign 18 ((.const 0)))) ((.seq ((.mustTerminate ((.call ((some ([20], (live32, live33), .skip, 69, 2))) ((some 25)) [14, 18, 16, 6, 4] none)))) ((.seq ((.assign 22 ((.const 4)))) ((.seq ((.assign 24 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 22)) (.const 1))])])))))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 16 4 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 16), (.var 4)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live34, live35), .skip, 69, 3))) ((some 13)) [16, 4] none)))))) ((.move 2 [(26, 1)])))))))) ((.call none ((some 69)) [0, 24, 26, 6] none))))))))))))))))))))), 4) =>
      decide (live32 = Flapjack.sptListInsert [0] .ln) &&
      decide (live33 = Flapjack.sptListInsert [2, 4, 6, 16] .ln) &&
      decide (live34 = Flapjack.sptListInsert [0] .ln) &&
      decide (live35 = Flapjack.sptListInsert [6, 24] .ln)
  | _ => false

private def matches8 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (72, 2, (.seq ((.assign 6 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 16)])))))) ((.seq ((.ite .equal 6 ((.imm 0)) ((.assign 8 (.const 18))) ((.assign 8 (.const 2))))) ((.ite .equal 8 ((.imm 18)) ((.seq ((.assign 10 (.const 2))) ((.seq ((.assign 12 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 8)])))))) ((.seq ((.call ((some ([14], (live36, live37), .skip, 72, 2))) none [10, 4, 12] none)) ((.seq ((.seq ((.assign 1 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 3 ((.const 281474976710715)))) ((.seq ((.store ((.var 1)) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 14)) ((.assign 16 (.const 2))))))))))) ((.return 0 [14])))))))))) ((.seq ((.assign 20 (.const 2))) ((.seq ((.call ((some ([22], (live38, live39), .skip, 72, 3))) ((some 72)) [20, 4] none)) ((.seq ((.seq ((.assign 1 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 3 ((.const 281474976710715)))) ((.seq ((.store ((.var 1)) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 22)) ((.assign 24 (.const 2))))))))))) ((.return 0 [22]))))))))))))), 4) =>
      decide (live36 = Flapjack.sptListInsert [0] .ln) &&
      decide (live37 = Flapjack.sptListInsert [2] .ln) &&
      decide (live38 = Flapjack.sptListInsert [0] .ln) &&
      decide (live39 = Flapjack.sptListInsert [2] .ln)
  | _ => false

private def matches9 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (76, 0, (.seq ((.assign 2 ((.const 4)))) ((.seq ((.call ((some ([4], (live40, .ln), .skip, 76, 2))) ((some 62)) [2] none)) ((.seq ((.assign 6 (.const 2))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 16)])) 6)) ((.assign 8 (.const 2))))) ((.call none ((some 80)) [0] none))))))))), 3) =>
      decide (live40 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches10 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (80, 0, (.seq ((.assign 2 ((.const 4)))) ((.seq ((.call ((some ([4], (live41, .ln), .skip, 80, 2))) ((some 62)) [2] none)) ((.seq ((.assign 6 (.const 2))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 24)])) 6)) ((.assign 8 (.const 2))))) ((.call none ((some 84)) [0] none))))))))), 3) =>
      decide (live41 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches11 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (84, 0, (.seq ((.call ((some ([2], (live42, .ln), .skip, 84, 2))) ((some 73)) [] none)) ((.seq ((.assign 4 (.const 2))) ((.call none ((some 88)) [0] none))))), 3) =>
      decide (live42 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches12 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (73, 0, (.return 0 [2]), 2) =>
      true
  | _ => false

private def matches13 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (88, 0, (.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 16)) ((.seq .skip ((.seq ((.assign 1 ((.const 16)))) ((.seq ((.alloc 1 (live43, .ln))) .skip)))))) .skip)))) ((.seq ((.assign 2 (.const 2))) ((.seq ((.seq ((.set .triggerGC ((.op .sub [(.lookup .triggerGC), (.const 16)])))) ((.seq ((.assign 1 ((.op .sub [(.lookup .endOfHeap), (.const 16)])))) ((.seq ((.set .endOfHeap ((.var 1)))) ((.seq ((.assign 3 ((.const 281474976710667)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 2)) .skip)))) ((.assign 4 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 1)])))))))))))))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 32)])) 4)) ((.assign 6 (.const 2))))) ((.call none ((some 92)) [0] none))))))))), 2) =>
      decide (live43 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches14 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (92, 0, (.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 16)) ((.seq .skip ((.seq ((.assign 1 ((.const 16)))) ((.seq ((.alloc 1 (live44, .ln))) .skip)))))) .skip)))) ((.seq ((.assign 2 ((.const 4)))) ((.seq ((.seq ((.set .triggerGC ((.op .sub [(.lookup .triggerGC), (.const 16)])))) ((.seq ((.assign 1 ((.op .sub [(.lookup .endOfHeap), (.const 16)])))) ((.seq ((.set .endOfHeap ((.var 1)))) ((.seq ((.assign 3 ((.const 281474976710667)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 2)) .skip)))) ((.assign 4 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 1)])))))))))))))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 40)])) 4)) ((.assign 8 (.const 2))))) ((.return 0 [8]))))))))), 2) =>
      decide (live44 = Flapjack.sptListInsert [0] .ln)
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0, entry1, entry2, entry3, entry4, entry5, entry6, entry7, entry8, entry9, entry10, entry11, entry12, entry13, entry14] =>
      matches0 entry0 &&
      matches1 entry1 &&
      matches2 entry2 &&
      matches3 entry3 &&
      matches4 entry4 &&
      matches5 entry5 &&
      matches6 entry6 &&
      matches7 entry7 &&
      matches8 entry8 &&
      matches9 entry9 &&
      matches10 entry10 &&
      matches11 entry11 &&
      matches12 entry12 &&
      matches13 entry13 &&
      matches14 entry14
  | _ => false

end Flapjack.Test.ReferenceCakeWordOracle
