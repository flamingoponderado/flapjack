-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang
import Flapjack.Test.CakeWordOracleHelpers

namespace Flapjack.Test.FullBvlOptimizedCakeWordOracle

open Flapjack.Test.CakeWordOracleHelpers

private def matches_fragment72 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 22 ((.imm 18)) ((.seq ((.assign 24 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 8)])))))) ((.seq ((.call ((some ([26], (live84, .ln), .skip, 73, 4))) none [2, 4, 24] none)) ((.seq ((.assign 28 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 26)) (.const 5))]), (.const 16)])))))) ((.seq ((.ite .equal 28 ((.imm 0)) ((.assign 30 (.const 18))) ((.assign 30 (.const 2))))) ((.ite .equal 30 ((.imm 18)) ((.seq ((.assign 32 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 26)) (.const 5))]), (.const 8)])))))) ((.call none none [0, 26, 32] none)))) ((.call none ((some 72)) [0, 26] none)))))))))))) ((.seq ((.assign 40 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 8)])))))) ((.seq ((.call ((some ([42], (live85, .ln), .skip, 73, 5))) none [14, 2, 4, 40] none)) ((.seq ((.assign 44 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 42)) (.const 5))]), (.const 16)])))))) ((.seq ((.ite .equal 44 ((.imm 0)) ((.assign 46 (.const 18))) ((.assign 46 (.const 2))))) ((.ite .equal 46 ((.imm 18)) ((.seq ((.assign 48 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 42)) (.const 5))]), (.const 8)])))))) ((.call none none [0, 42, 48] none)))) ((.call none ((some 72)) [0, 42] none)))))))))))))) =>
      decide (live84 = Flapjack.sptListInsert [0] .ln) &&
      decide (live85 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment73 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 40)) ((.seq .skip ((.seq ((.assign 1 ((.const 40)))) ((.seq ((.alloc 1 (live94, live95))) .skip)))))) .skip)))) ((.seq ((.assign 72 ((.load ((.op .add [(.lookup .globReal), (.const 16)])))))) ((.seq ((.assign 74 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 72)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 70)) (.const 1))])])))))) ((.seq ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 3 ((.const 1125899906843123)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 74)) ((.seq ((.store ((.op .add [(.var 1), (.const 16)])) 14)) ((.seq ((.store ((.op .add [(.var 1), (.const 24)])) 4)) ((.seq ((.store ((.op .add [(.var 1), (.const 32)])) 2)) .skip)))))))))) ((.seq ((.assign 76 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 15)])))) ((.set .nextFree ((.op .add [(.var 1), (.const 40)])))))))))))) ((.return 0 [76])))))))))) =>
      decide (live94 = Flapjack.sptListInsert [0] .ln) &&
      decide (live95 = Flapjack.sptListInsert [2, 4, 14, 70] .ln)
  | _ => false

private def matches_fragment74 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 64 60 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 64), (.var 60)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live86, live87), .skip, 73, 6))) ((some 13)) [64, 60] none)))))) ((.move 2 [(66, 1)])))))))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 66)) (.const 1))))) ((.seq ((.inst ((.arith ((.longMul 3 1 1 60)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.op .and [(.const 1), (.op .or [(.var 66), (.var 60)])])])))) ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 1))))) ((.seq ((.ite .equal 3 ((.imm 0)) .skip ((.mustTerminate ((.call ((some ([1], (live88, live89), .skip, 73, 7))) ((some 15)) [66, 60] none)))))) ((.move 2 [(68, 1)])))))))))))) ((.seq ((.seq ((.assign 1 ((.op .or [(.var 68), (.var 62)])))) ((.seq ((.assign 1 ((.op .or [(.var 1), (.shift .lsr ((.var 1)) (.const 63))])))) ((.ite .test 1 ((.imm 1)) ((.seq ((.assign 1 ((.const 0)))) ((.seq ((.mustTerminate ((.call ((some ([1], (live90, live91), .skip, 73, 9))) ((some 23)) [1, 68, 62] none)))) ((.assign 70 ((.shift .lsl ((.var 1)) (.const 2))))))))) ((.seq ((.mustTerminate ((.call ((some ([1], (live92, live93), .skip, 73, 8))) ((some 16)) [68, 62] none)))) ((.move 2 [(70, 1)])))))))))) fragment73)))))) =>
      decide (live86 = Flapjack.sptListInsert [0] .ln) &&
      decide (live87 = Flapjack.sptListInsert [2, 4, 14, 60, 62] .ln) &&
      decide (live88 = Flapjack.sptListInsert [0] .ln) &&
      decide (live89 = Flapjack.sptListInsert [2, 4, 14, 62] .ln) &&
      decide (live90 = Flapjack.sptListInsert [0] .ln) &&
      decide (live91 = Flapjack.sptListInsert [2, 4, 14] .ln) &&
      decide (live92 = Flapjack.sptListInsert [0] .ln) &&
      decide (live93 = Flapjack.sptListInsert [2, 4, 14] .ln) &&
      matches_fragment73 fragment73
  | _ => false

private def matches_fragment75 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 5)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 106)) ((.seq ((.store ((.op .add [(.var 1), (.const 16)])) 14)) ((.seq ((.store ((.op .add [(.var 1), (.const 24)])) 84)) ((.seq ((.store ((.op .add [(.var 1), (.const 32)])) 2)) .skip)))))))))) ((.seq ((.seq ((.assign 3 ((.op .or [(.const 1), (.shift .lsl ((.op .sub [(.lookup .nextFree), (.lookup .currHeap)])) (.const 5))])))) ((.seq ((.ite .lower 9 ((.imm 1)) ((.assign 3 ((.op .or [(.var 3), (.shift .lsl ((.var 9)) (.const 3))])))) ((.assign 3 ((.op .or [(.var 3), (.const 8)])))))) ((.ite .lower 7 ((.imm 3)) ((.assign 3 ((.op .or [(.var 3), (.shift .lsl ((.var 7)) (.const 1))])))) ((.assign 3 ((.op .or [(.var 3), (.const 6)])))))))))) ((.seq ((.set .nextFree ((.op .add [(.var 1), (.const 8), (.shift .lsl ((.var 7)) (.const 3))])))) ((.seq ((.assign 15 ((.var 82)))) ((.seq ((.assign 13 ((.op .add [(.var 1), (.const 40)])))) ((.seq ((.assign 11 ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 8), (.shift .lsl ((.var 112)) (.const 1))])))) ((.ite .test 15 ((.reg 15)) ((.assign 114 ((.var 3)))) ((.mustTerminate ((.call ((some ([114], (live117, .ln), .skip, 73, 19))) ((some 24)) [15, 11, 13, 3] none)))))))))))))))))) =>
      decide (live117 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment76 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 108 82 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 108), (.var 82)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live112, live113), .skip, 73, 18))) ((some 13)) [108, 82] none)))))) ((.move 2 [(110, 1)])))))))) ((.seq ((.assign 112 ((.const 12)))) ((.seq ((.seq ((.ite .test 110 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live114, .ln))))))) ((.seq ((.assign 1 ((.var 110)))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live115, live116))) .skip)))) .skip)))))))) ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 5 ((.op .or [(.shift .lsl ((.var 110)) (.const 46)), (.const 499)])))) ((.seq ((.assign 7 ((.shift .lsr ((.var 110)) (.const 2))))) ((.seq ((.assign 9 ((.const 31)))) fragment75)))))))))))))) ((.return 0 [114])))))))) =>
      decide (live112 = Flapjack.sptListInsert [0] .ln) &&
      decide (live113 = Flapjack.sptListInsert [2, 4, 14, 82, 84, 106] .ln) &&
      decide (live114 = Flapjack.sptListInsert [0] .ln) &&
      decide (live115 = Flapjack.sptListInsert [0] .ln) &&
      decide (live116 = Flapjack.sptListInsert [2, 4, 14, 82, 84, 106, 110, 112] .ln) &&
      matches_fragment75 fragment75
  | _ => false

private def matches_fragment77 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 1 ((.op .or [(.var 98), (.var 92)])))) ((.seq ((.assign 1 ((.op .or [(.var 1), (.shift .lsr ((.var 1)) (.const 63))])))) ((.ite .test 1 ((.imm 1)) ((.seq ((.assign 1 ((.const 0)))) ((.seq ((.mustTerminate ((.call ((some ([1], (live106, live107), .skip, 73, 16))) ((some 23)) [1, 98, 92] none)))) ((.assign 100 ((.shift .lsl ((.var 1)) (.const 2))))))))) ((.seq ((.mustTerminate ((.call ((some ([1], (live108, live109), .skip, 73, 15))) ((some 16)) [98, 92] none)))) ((.move 2 [(100, 1)])))))))))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 100 82 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 100), (.var 82)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live110, live111), .skip, 73, 17))) ((some 13)) [100, 82] none)))))) ((.move 2 [(102, 1)])))))))) ((.seq ((.assign 104 ((.load ((.op .add [(.lookup .globReal), (.const 16)])))))) ((.seq ((.assign 106 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 104)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 102)) (.const 1))])])))))) ((.seq ((.assign 108 ((.const 16)))) fragment76)))))))))) =>
      decide (live106 = Flapjack.sptListInsert [0] .ln) &&
      decide (live107 = Flapjack.sptListInsert [2, 4, 14, 82, 84] .ln) &&
      decide (live108 = Flapjack.sptListInsert [0] .ln) &&
      decide (live109 = Flapjack.sptListInsert [2, 4, 14, 82, 84] .ln) &&
      decide (live110 = Flapjack.sptListInsert [0] .ln) &&
      decide (live111 = Flapjack.sptListInsert [2, 4, 14, 82, 84] .ln) &&
      matches_fragment76 fragment76
  | _ => false

private def matches_fragment78 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 88 82 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 88), (.var 82)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live100, live101), .skip, 73, 12))) ((some 13)) [88, 82] none)))))) ((.move 2 [(90, 1)])))))))) ((.seq ((.assign 92 ((.const 8)))) ((.seq ((.assign 94 ((.const 18446744073709551612)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 94 90 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 94), (.var 90)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live102, live103), .skip, 73, 13))) ((some 13)) [94, 90] none)))))) ((.move 2 [(96, 1)])))))))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 96)) (.const 1))))) ((.seq ((.inst ((.arith ((.longMul 3 1 1 90)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.op .and [(.const 1), (.op .or [(.var 96), (.var 90)])])])))) ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 1))))) ((.seq ((.ite .equal 3 ((.imm 0)) .skip ((.mustTerminate ((.call ((some ([1], (live104, live105), .skip, 73, 14))) ((some 15)) [96, 90] none)))))) ((.move 2 [(98, 1)])))))))))))) fragment77)))))))))) =>
      decide (live100 = Flapjack.sptListInsert [0] .ln) &&
      decide (live101 = Flapjack.sptListInsert [2, 4, 14, 82, 84] .ln) &&
      decide (live102 = Flapjack.sptListInsert [0] .ln) &&
      decide (live103 = Flapjack.sptListInsert [2, 4, 14, 82, 84, 90, 92] .ln) &&
      decide (live104 = Flapjack.sptListInsert [0] .ln) &&
      decide (live105 = Flapjack.sptListInsert [2, 4, 14, 82, 84, 92] .ln) &&
      matches_fragment77 fragment77
  | _ => false

private def matches_fragment79 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 58 ((.imm 18)) ((.seq ((.assign 60 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 16)])))))) ((.seq ((.assign 62 ((.const 8)))) ((.seq ((.assign 64 ((.const 18446744073709551612)))) fragment74)))))) ((.seq ((.ite .test 4 ((.imm 1)) ((.assign 78 ((.const 0)))) ((.assign 78 ((.shift .lsl ((.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) (.const 48))) (.const 2))))))) ((.seq ((.assign 80 ((.const 18446744073709551604)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 80 78 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 80), (.var 78)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live96, live97), .skip, 73, 10))) ((some 13)) [80, 78] none)))))) ((.move 2 [(82, 1)])))))))) ((.seq ((.assign 84 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 24)])))))) ((.seq ((.assign 86 ((.const 4)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 86 14 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 86), (.var 14)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live98, live99), .skip, 73, 11))) ((some 13)) [86, 14] none)))))) ((.move 2 [(88, 1)])))))))) fragment78)))))))))))))) =>
      decide (live96 = Flapjack.sptListInsert [0] .ln) &&
      decide (live97 = Flapjack.sptListInsert [2, 4, 14] .ln) &&
      decide (live98 = Flapjack.sptListInsert [0] .ln) &&
      decide (live99 = Flapjack.sptListInsert [2, 4, 14, 82, 84] .ln) &&
      matches_fragment74 fragment74 &&
      matches_fragment78 fragment78
  | _ => false

private def matches_fragment80 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.assign 16 ((.const 0)))) ((.seq ((.seq ((.assign 1 ((.var 14)))) ((.seq ((.assign 3 ((.var 16)))) ((.seq ((.assign 5 ((.op .or [(.var 1), (.var 3)])))) ((.seq ((.ite .test 5 ((.imm 1)) .skip ((.seq ((.mustTerminate ((.call ((some ([1], (live82, live83), .skip, 73, 3))) ((some 19)) [1, 3] none)))) ((.assign 3 ((.const 1)))))))) ((.ite .less 1 ((.reg 3)) ((.assign 18 (.const 18))) ((.assign 18 (.const 2))))))))))))) ((.ite .equal 18 ((.imm 18)) ((.seq ((.assign 20 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 16)])))))) ((.seq ((.ite .less 20 ((.imm 4)) ((.assign 22 (.const 18))) ((.assign 22 (.const 2))))) fragment72)))) ((.seq ((.seq ((.assign 1 ((.var 4)))) ((.seq ((.ite .test 4 ((.imm 1)) .skip ((.assign 1 ((.op .and [(.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]))), (.const 281474976710654)])))))) ((.ite .equal 1 ((.imm 482)) ((.assign 58 (.const 18))) ((.assign 58 (.const 2))))))))) fragment79)))))))) =>
      decide (live82 = Flapjack.sptListInsert [0] .ln) &&
      decide (live83 = Flapjack.sptListInsert [2, 4, 14] .ln) &&
      matches_fragment72 fragment72 &&
      matches_fragment79 fragment79
  | _ => false

private def matches_fragment81 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 24 ((.imm 18)) ((.seq ((.assign 26 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 8)) (.const 5))]), (.const 8)])))))) ((.seq ((.call ((some ([28], (live122, live123), .skip, 77, 3))) none [6, 8, 26] none)) ((.seq ((.assign 30 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 28)) (.const 5))]), (.const 16)])))))) ((.seq ((.ite .equal 30 ((.imm 0)) ((.assign 32 (.const 18))) ((.assign 32 (.const 2))))) ((.ite .equal 32 ((.imm 18)) ((.seq ((.assign 34 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 28)) (.const 5))]), (.const 8)])))))) ((.call none none [0, 4, 28, 34] none)))) ((.call none ((some 72)) [0, 4, 28] none)))))))))))) ((.seq ((.assign 42 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 8)) (.const 5))]), (.const 8)])))))) ((.seq ((.call ((some ([44], (live124, .ln), .skip, 77, 4))) none [4, 6, 8, 42] none)) ((.seq ((.assign 46 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 44)) (.const 5))]), (.const 16)])))))) ((.seq ((.ite .equal 46 ((.imm 0)) ((.assign 48 (.const 18))) ((.assign 48 (.const 2))))) ((.ite .equal 48 ((.imm 18)) ((.seq ((.assign 50 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 44)) (.const 5))]), (.const 8)])))))) ((.call none none [0, 44, 50] none)))) ((.call none ((some 72)) [0, 44] none)))))))))))))) =>
      decide (live122 = Flapjack.sptListInsert [0] .ln) &&
      decide (live123 = Flapjack.sptListInsert [4] .ln) &&
      decide (live124 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment82 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 48)) ((.seq .skip ((.seq ((.assign 1 ((.const 48)))) ((.seq ((.alloc 1 (live135, live136))) .skip)))))) .skip)))) ((.seq ((.assign 78 ((.load ((.op .add [(.lookup .globReal), (.const 16)])))))) ((.seq ((.assign 80 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 78)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 76)) (.const 1))])])))))) ((.seq ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 3 ((.const 1407374883553779)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 80)) ((.seq ((.store ((.op .add [(.var 1), (.const 16)])) 2)) ((.seq ((.store ((.op .add [(.var 1), (.const 24)])) 8)) ((.seq ((.store ((.op .add [(.var 1), (.const 32)])) 4)) ((.seq ((.store ((.op .add [(.var 1), (.const 40)])) 6)) .skip)))))))))))) ((.seq ((.assign 82 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 15)])))) ((.set .nextFree ((.op .add [(.var 1), (.const 48)])))))))))))) ((.return 0 [82])))))))))) =>
      decide (live135 = Flapjack.sptListInsert [0] .ln) &&
      decide (live136 = Flapjack.sptListInsert [2, 4, 6, 8, 76] .ln)
  | _ => false

private def matches_fragment83 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 68)) (.const 1))))) ((.seq ((.inst ((.arith ((.longMul 3 1 1 62)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.op .and [(.const 1), (.op .or [(.var 68), (.var 62)])])])))) ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 1))))) ((.seq ((.ite .equal 3 ((.imm 0)) .skip ((.mustTerminate ((.call ((some ([1], (live127, live128), .skip, 77, 6))) ((some 15)) [68, 62] none)))))) ((.move 2 [(70, 1)])))))))))))) ((.seq ((.seq ((.assign 1 ((.op .or [(.var 70), (.var 64)])))) ((.seq ((.assign 1 ((.op .or [(.var 1), (.shift .lsr ((.var 1)) (.const 63))])))) ((.ite .test 1 ((.imm 1)) ((.seq ((.assign 1 ((.const 0)))) ((.seq ((.mustTerminate ((.call ((some ([1], (live129, live130), .skip, 77, 8))) ((some 23)) [1, 70, 64] none)))) ((.assign 72 ((.shift .lsl ((.var 1)) (.const 2))))))))) ((.seq ((.mustTerminate ((.call ((some ([1], (live131, live132), .skip, 77, 7))) ((some 16)) [70, 64] none)))) ((.move 2 [(72, 1)])))))))))) ((.seq ((.assign 74 ((.const 4)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 74 72 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 74), (.var 72)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live133, live134), .skip, 77, 9))) ((some 13)) [74, 72] none)))))) ((.move 2 [(76, 1)])))))))) fragment82)))))))) =>
      decide (live127 = Flapjack.sptListInsert [0] .ln) &&
      decide (live128 = Flapjack.sptListInsert [2, 4, 6, 8, 64] .ln) &&
      decide (live129 = Flapjack.sptListInsert [0] .ln) &&
      decide (live130 = Flapjack.sptListInsert [2, 4, 6, 8] .ln) &&
      decide (live131 = Flapjack.sptListInsert [0] .ln) &&
      decide (live132 = Flapjack.sptListInsert [2, 4, 6, 8] .ln) &&
      decide (live133 = Flapjack.sptListInsert [0] .ln) &&
      decide (live134 = Flapjack.sptListInsert [2, 4, 6, 8] .ln) &&
      matches_fragment82 fragment82
  | _ => false

private def matches_fragment84 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 5)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 116)) ((.seq ((.store ((.op .add [(.var 1), (.const 16)])) 2)) ((.seq ((.store ((.op .add [(.var 1), (.const 24)])) 90)) ((.seq ((.store ((.op .add [(.var 1), (.const 32)])) 4)) ((.seq ((.store ((.op .add [(.var 1), (.const 40)])) 6)) .skip)))))))))))) ((.seq ((.seq ((.assign 3 ((.op .or [(.const 1), (.shift .lsl ((.op .sub [(.lookup .nextFree), (.lookup .currHeap)])) (.const 5))])))) ((.seq ((.ite .lower 9 ((.imm 1)) ((.assign 3 ((.op .or [(.var 3), (.shift .lsl ((.var 9)) (.const 3))])))) ((.assign 3 ((.op .or [(.var 3), (.const 8)])))))) ((.ite .lower 7 ((.imm 3)) ((.assign 3 ((.op .or [(.var 3), (.shift .lsl ((.var 7)) (.const 1))])))) ((.assign 3 ((.op .or [(.var 3), (.const 6)])))))))))) ((.seq ((.set .nextFree ((.op .add [(.var 1), (.const 8), (.shift .lsl ((.var 7)) (.const 3))])))) ((.seq ((.assign 15 ((.var 88)))) ((.seq ((.assign 13 ((.op .add [(.var 1), (.const 48)])))) ((.seq ((.assign 11 ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 8)) (.const 5))]), (.const 8), (.shift .lsl ((.var 122)) (.const 1))])))) ((.ite .test 15 ((.reg 15)) ((.assign 124 ((.var 3)))) ((.mustTerminate ((.call ((some ([124], (live160, .ln), .skip, 77, 20))) ((some 24)) [15, 11, 13, 3] none)))))))))))))))))) =>
      decide (live160 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment85 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 118 88 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 118), (.var 88)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live155, live156), .skip, 77, 19))) ((some 13)) [118, 88] none)))))) ((.move 2 [(120, 1)])))))))) ((.seq ((.assign 122 ((.const 12)))) ((.seq ((.seq ((.ite .test 120 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live157, .ln))))))) ((.seq ((.assign 1 ((.var 120)))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live158, live159))) .skip)))) .skip)))))))) ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 5 ((.op .or [(.shift .lsl ((.var 120)) (.const 46)), (.const 499)])))) ((.seq ((.assign 7 ((.shift .lsr ((.var 120)) (.const 2))))) ((.seq ((.assign 9 ((.const 31)))) fragment84)))))))))))))) ((.return 0 [124])))))))) =>
      decide (live155 = Flapjack.sptListInsert [0] .ln) &&
      decide (live156 = Flapjack.sptListInsert [2, 4, 6, 8, 88, 90, 116] .ln) &&
      decide (live157 = Flapjack.sptListInsert [0] .ln) &&
      decide (live158 = Flapjack.sptListInsert [0] .ln) &&
      decide (live159 = Flapjack.sptListInsert [2, 4, 6, 8, 88, 90, 116, 120, 122] .ln) &&
      matches_fragment84 fragment84
  | _ => false

private def matches_fragment86 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 1 ((.op .or [(.var 108), (.var 102)])))) ((.seq ((.assign 1 ((.op .or [(.var 1), (.shift .lsr ((.var 1)) (.const 63))])))) ((.ite .test 1 ((.imm 1)) ((.seq ((.assign 1 ((.const 0)))) ((.seq ((.mustTerminate ((.call ((some ([1], (live149, live150), .skip, 77, 17))) ((some 23)) [1, 108, 102] none)))) ((.assign 110 ((.shift .lsl ((.var 1)) (.const 2))))))))) ((.seq ((.mustTerminate ((.call ((some ([1], (live151, live152), .skip, 77, 16))) ((some 16)) [108, 102] none)))) ((.move 2 [(110, 1)])))))))))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 110 100 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 110), (.var 100)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live153, live154), .skip, 77, 18))) ((some 13)) [110, 100] none)))))) ((.move 2 [(112, 1)])))))))) ((.seq ((.assign 114 ((.load ((.op .add [(.lookup .globReal), (.const 16)])))))) ((.seq ((.assign 116 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 114)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 112)) (.const 1))])])))))) ((.seq ((.assign 118 ((.const 20)))) fragment85)))))))))) =>
      decide (live149 = Flapjack.sptListInsert [0] .ln) &&
      decide (live150 = Flapjack.sptListInsert [2, 4, 6, 8, 88, 90, 100] .ln) &&
      decide (live151 = Flapjack.sptListInsert [0] .ln) &&
      decide (live152 = Flapjack.sptListInsert [2, 4, 6, 8, 88, 90, 100] .ln) &&
      decide (live153 = Flapjack.sptListInsert [0] .ln) &&
      decide (live154 = Flapjack.sptListInsert [2, 4, 6, 8, 88, 90] .ln) &&
      matches_fragment85 fragment85
  | _ => false

private def matches_fragment87 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 98 88 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 98), (.var 88)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live143, live144), .skip, 77, 13))) ((some 13)) [98, 88] none)))))) ((.move 2 [(100, 1)])))))))) ((.seq ((.assign 102 ((.const 8)))) ((.seq ((.assign 104 ((.const 18446744073709551612)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 104 96 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 104), (.var 96)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live145, live146), .skip, 77, 14))) ((some 13)) [104, 96] none)))))) ((.move 2 [(106, 1)])))))))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 106)) (.const 1))))) ((.seq ((.inst ((.arith ((.longMul 3 1 1 96)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.op .and [(.const 1), (.op .or [(.var 106), (.var 96)])])])))) ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 1))))) ((.seq ((.ite .equal 3 ((.imm 0)) .skip ((.mustTerminate ((.call ((some ([1], (live147, live148), .skip, 77, 15))) ((some 15)) [106, 96] none)))))) ((.move 2 [(108, 1)])))))))))))) fragment86)))))))))) =>
      decide (live143 = Flapjack.sptListInsert [0] .ln) &&
      decide (live144 = Flapjack.sptListInsert [2, 4, 6, 8, 88, 90, 96] .ln) &&
      decide (live145 = Flapjack.sptListInsert [0] .ln) &&
      decide (live146 = Flapjack.sptListInsert [2, 4, 6, 8, 88, 90, 96, 100, 102] .ln) &&
      decide (live147 = Flapjack.sptListInsert [0] .ln) &&
      decide (live148 = Flapjack.sptListInsert [2, 4, 6, 8, 88, 90, 100, 102] .ln) &&
      matches_fragment86 fragment86
  | _ => false

private def matches_fragment88 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 86 84 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 86), (.var 84)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live137, live138), .skip, 77, 10))) ((some 13)) [86, 84] none)))))) ((.move 2 [(88, 1)])))))))) ((.seq ((.assign 90 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 8)) (.const 5))]), (.const 24)])))))) ((.seq ((.assign 92 ((.const 8)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 92 2 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 92), (.var 2)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live139, live140), .skip, 77, 11))) ((some 13)) [92, 2] none)))))) ((.move 2 [(94, 1)])))))))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 94 88 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 94), (.var 88)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live141, live142), .skip, 77, 12))) ((some 13)) [94, 88] none)))))) ((.move 2 [(96, 1)])))))))) ((.seq ((.assign 98 ((.const 4)))) fragment87)))))))))))) =>
      decide (live137 = Flapjack.sptListInsert [0] .ln) &&
      decide (live138 = Flapjack.sptListInsert [2, 4, 6, 8] .ln) &&
      decide (live139 = Flapjack.sptListInsert [0] .ln) &&
      decide (live140 = Flapjack.sptListInsert [2, 4, 6, 8, 88, 90] .ln) &&
      decide (live141 = Flapjack.sptListInsert [0] .ln) &&
      decide (live142 = Flapjack.sptListInsert [2, 4, 6, 8, 88, 90] .ln) &&
      matches_fragment87 fragment87
  | _ => false

private def matches_fragment89 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 20 ((.imm 18)) ((.seq ((.assign 22 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 8)) (.const 5))]), (.const 16)])))))) ((.seq ((.ite .less 22 ((.imm 4)) ((.assign 24 (.const 18))) ((.assign 24 (.const 2))))) fragment81)))) ((.seq ((.seq ((.assign 1 ((.var 8)))) ((.seq ((.ite .test 8 ((.imm 1)) .skip ((.assign 1 ((.op .and [(.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 8)) (.const 5))]))), (.const 281474976710654)])))))) ((.ite .equal 1 ((.imm 482)) ((.assign 60 (.const 18))) ((.assign 60 (.const 2))))))))) ((.ite .equal 60 ((.imm 18)) ((.seq ((.assign 62 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 8)) (.const 5))]), (.const 16)])))))) ((.seq ((.assign 64 ((.const 8)))) ((.seq ((.assign 66 ((.const 18446744073709551612)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 66 62 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 66), (.var 62)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live125, live126), .skip, 77, 5))) ((some 13)) [66, 62] none)))))) ((.move 2 [(68, 1)])))))))) fragment83)))))))) ((.seq ((.ite .test 8 ((.imm 1)) ((.assign 84 ((.const 0)))) ((.assign 84 ((.shift .lsl ((.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 8)) (.const 5))])))) (.const 48))) (.const 2))))))) ((.seq ((.assign 86 ((.const 18446744073709551604)))) fragment88)))))))))) =>
      decide (live125 = Flapjack.sptListInsert [0] .ln) &&
      decide (live126 = Flapjack.sptListInsert [2, 4, 6, 8, 62, 64] .ln) &&
      matches_fragment81 fragment81 &&
      matches_fragment83 fragment83 &&
      matches_fragment88 fragment88
  | _ => false

private def matches57 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (64, 1, (.seq ((.assign 2 ((.const 0)))) ((.seq ((.assign 4 ((.const 12)))) fragment67))), 0) =>
      shared_matches_fragment67 fragment67
  | _ => false

private def matches63 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (72, 3, (.call none ((some 73)) [0, 2, 4] none), 0) =>
      true
  | _ => false

private def matches64 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (73, 3, (.seq ((.assign 10 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 16)])))))) ((.seq ((.assign 12 ((.const 18446744073709551612)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 12 10 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 12), (.var 10)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live80, live81), .skip, 73, 2))) ((some 13)) [12, 10] none)))))) ((.move 2 [(14, 1)])))))))) fragment80))))), 0) =>
      decide (live80 = Flapjack.sptListInsert [0] .ln) &&
      decide (live81 = Flapjack.sptListInsert [2, 4] .ln) &&
      matches_fragment80 fragment80
  | _ => false

private def matches65 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (76, 4, (.seq ((.assign 8 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.const 16)])))))) ((.seq ((.assign 10 ((.const 18446744073709551608)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 10 8 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 10), (.var 8)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live118, live119), .skip, 76, 2))) ((some 13)) [10, 8] none)))))) ((.move 2 [(12, 1)])))))))) ((.call none ((some 77)) [0, 12, 2, 4, 6] none))))))), 0) =>
      decide (live118 = Flapjack.sptListInsert [0] .ln) &&
      decide (live119 = Flapjack.sptListInsert [2, 4, 6] .ln)
  | _ => false

private def matches66 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (77, 5, (.seq ((.assign 18 ((.const 0)))) ((.seq ((.seq ((.assign 1 ((.var 2)))) ((.seq ((.assign 3 ((.var 18)))) ((.seq ((.assign 5 ((.op .or [(.var 1), (.var 3)])))) ((.seq ((.ite .test 5 ((.imm 1)) .skip ((.seq ((.mustTerminate ((.call ((some ([1], (live120, live121), .skip, 77, 2))) ((some 19)) [1, 3] none)))) ((.assign 3 ((.const 1)))))))) ((.ite .less 1 ((.reg 3)) ((.assign 20 (.const 18))) ((.assign 20 (.const 2))))))))))))) fragment89))), 0) =>
      decide (live120 = Flapjack.sptListInsert [0] .ln) &&
      decide (live121 = Flapjack.sptListInsert [2, 4, 6, 8] .ln) &&
      matches_fragment89 fragment89
  | _ => false

private def matches67 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (80, 3, (.seq ((.assign 6 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 24)])))))) ((.seq ((.assign 8 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 32)])))))) ((.seq ((.assign 10 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.const 8)])))))) ((.call none none [0, 2, 8, 6, 10] none))))))), 0) =>
      true
  | _ => false

private def matches68 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (84, 3, (.seq ((.assign 6 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 16)])))))) fragment90), 0) =>
      shared_matches_fragment90 fragment90
  | _ => false

private def matches69 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (88, 1, (.seq ((.assign 2 ((.const 4)))) ((.seq ((.call ((some ([4], (live165, .ln), .skip, 88, 2))) ((some 62)) [2] none)) ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 16)) ((.seq .skip ((.seq ((.assign 1 ((.const 16)))) ((.seq ((.alloc 1 (live166, .ln))) .skip)))))) .skip)))) ((.seq ((.locValue 6 80)) ((.seq ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 3 ((.const 281474976710659)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 6)) .skip)))) ((.seq ((.assign 8 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 3)])))) ((.set .nextFree ((.op .add [(.var 1), (.const 16)])))))))))))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 16)])) 8)) ((.assign 10 (.const 2))))) ((.call none ((some 92)) [0] none))))))))))))), 0) =>
      decide (live165 = Flapjack.sptListInsert [0] .ln) &&
      decide (live166 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches70 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (92, 1, (.seq ((.assign 2 ((.const 4)))) ((.seq ((.call ((some ([4], (live167, .ln), .skip, 92, 2))) ((some 62)) [2] none)) ((.seq ((.assign 6 (.const 2))) ((.seq ((.assign 8 (.const 2))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 24)])) 8)) ((.assign 10 (.const 2))))) ((.call none ((some 96)) [0] none))))))))))), 0) =>
      decide (live167 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches71 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (96, 1, (.seq ((.assign 2 ((.const 8)))) ((.seq ((.call ((some ([4], (live168, .ln), .skip, 96, 2))) ((some 62)) [2] none)) ((.seq ((.assign 6 (.const 2))) ((.call none ((some 100)) [0] none))))))), 0) =>
      decide (live168 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches72 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (100, 1, (.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 16)) ((.seq .skip ((.seq ((.assign 1 ((.const 16)))) ((.seq ((.alloc 1 (live169, .ln))) .skip)))))) .skip)))) ((.seq ((.assign 2 (.const 2))) ((.seq ((.seq ((.set .triggerGC ((.op .sub [(.lookup .triggerGC), (.const 16)])))) ((.seq ((.assign 1 ((.op .sub [(.lookup .endOfHeap), (.const 16)])))) ((.seq ((.set .endOfHeap ((.var 1)))) ((.seq ((.assign 3 ((.const 281474976710667)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 2)) .skip)))) ((.assign 4 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 1)])))))))))))))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 32)])) 4)) ((.assign 6 (.const 2))))) ((.return 0 [6]))))))))), 0) =>
      decide (live169 = Flapjack.sptListInsert [0] .ln)
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  code.length == 73 &&
    (match code[0]? with | some entry => shared_matches0_3 entry | none => false) &&
    (match code[1]? with | some entry => shared_matches1_2 entry | none => false) &&
    (match code[2]? with | some entry => shared_matches2_2 entry | none => false) &&
    (match code[3]? with | some entry => shared_matches3_2 entry | none => false) &&
    (match code[4]? with | some entry => shared_matches4_2 entry | none => false) &&
    (match code[5]? with | some entry => shared_matches5_2 entry | none => false) &&
    (match code[6]? with | some entry => shared_matches6_2 entry | none => false) &&
    (match code[7]? with | some entry => shared_matches7_2 entry | none => false) &&
    (match code[8]? with | some entry => shared_matches8_2 entry | none => false) &&
    (match code[9]? with | some entry => shared_matches9_2 entry | none => false) &&
    (match code[10]? with | some entry => shared_matches10_2 entry | none => false) &&
    (match code[11]? with | some entry => shared_matches11_2 entry | none => false) &&
    (match code[12]? with | some entry => shared_matches12_2 entry | none => false) &&
    (match code[13]? with | some entry => shared_matches13_2 entry | none => false) &&
    (match code[14]? with | some entry => shared_matches14 entry | none => false) &&
    (match code[15]? with | some entry => shared_matches15 entry | none => false) &&
    (match code[16]? with | some entry => shared_matches16 entry | none => false) &&
    (match code[17]? with | some entry => shared_matches17 entry | none => false) &&
    (match code[18]? with | some entry => shared_matches18 entry | none => false) &&
    (match code[19]? with | some entry => shared_matches19 entry | none => false) &&
    (match code[20]? with | some entry => shared_matches20 entry | none => false) &&
    (match code[21]? with | some entry => shared_matches21 entry | none => false) &&
    (match code[22]? with | some entry => shared_matches22 entry | none => false) &&
    (match code[23]? with | some entry => shared_matches23 entry | none => false) &&
    (match code[24]? with | some entry => shared_matches24 entry | none => false) &&
    (match code[25]? with | some entry => shared_matches25 entry | none => false) &&
    (match code[26]? with | some entry => shared_matches26 entry | none => false) &&
    (match code[27]? with | some entry => shared_matches27 entry | none => false) &&
    (match code[28]? with | some entry => shared_matches28 entry | none => false) &&
    (match code[29]? with | some entry => shared_matches29 entry | none => false) &&
    (match code[30]? with | some entry => shared_matches30 entry | none => false) &&
    (match code[31]? with | some entry => shared_matches31 entry | none => false) &&
    (match code[32]? with | some entry => shared_matches32 entry | none => false) &&
    (match code[33]? with | some entry => shared_matches33 entry | none => false) &&
    (match code[34]? with | some entry => shared_matches34 entry | none => false) &&
    (match code[35]? with | some entry => shared_matches35 entry | none => false) &&
    (match code[36]? with | some entry => shared_matches36 entry | none => false) &&
    (match code[37]? with | some entry => shared_matches37 entry | none => false) &&
    (match code[38]? with | some entry => shared_matches38 entry | none => false) &&
    (match code[39]? with | some entry => shared_matches39 entry | none => false) &&
    (match code[40]? with | some entry => shared_matches40 entry | none => false) &&
    (match code[41]? with | some entry => shared_matches41 entry | none => false) &&
    (match code[42]? with | some entry => shared_matches42 entry | none => false) &&
    (match code[43]? with | some entry => shared_matches43 entry | none => false) &&
    (match code[44]? with | some entry => shared_matches44 entry | none => false) &&
    (match code[45]? with | some entry => shared_matches45 entry | none => false) &&
    (match code[46]? with | some entry => shared_matches46 entry | none => false) &&
    (match code[47]? with | some entry => shared_matches47 entry | none => false) &&
    (match code[48]? with | some entry => shared_matches48 entry | none => false) &&
    (match code[49]? with | some entry => shared_matches49 entry | none => false) &&
    (match code[50]? with | some entry => shared_matches50 entry | none => false) &&
    (match code[51]? with | some entry => shared_matches51 entry | none => false) &&
    (match code[52]? with | some entry => shared_matches52 entry | none => false) &&
    (match code[53]? with | some entry => shared_matches53 entry | none => false) &&
    (match code[54]? with | some entry => shared_matches54 entry | none => false) &&
    (match code[55]? with | some entry => shared_matches55 entry | none => false) &&
    (match code[56]? with | some entry => shared_matches56 entry | none => false) &&
    (match code[57]? with | some entry => matches57 entry | none => false) &&
    (match code[58]? with | some entry => shared_matches58 entry | none => false) &&
    (match code[59]? with | some entry => shared_matches59 entry | none => false) &&
    (match code[60]? with | some entry => shared_matches60 entry | none => false) &&
    (match code[61]? with | some entry => shared_matches61 entry | none => false) &&
    (match code[62]? with | some entry => shared_matches62 entry | none => false) &&
    (match code[63]? with | some entry => matches63 entry | none => false) &&
    (match code[64]? with | some entry => matches64 entry | none => false) &&
    (match code[65]? with | some entry => matches65 entry | none => false) &&
    (match code[66]? with | some entry => matches66 entry | none => false) &&
    (match code[67]? with | some entry => matches67 entry | none => false) &&
    (match code[68]? with | some entry => matches68 entry | none => false) &&
    (match code[69]? with | some entry => matches69 entry | none => false) &&
    (match code[70]? with | some entry => matches70 entry | none => false) &&
    (match code[71]? with | some entry => matches71 entry | none => false) &&
    (match code[72]? with | some entry => matches72 entry | none => false)

end Flapjack.Test.FullBvlOptimizedCakeWordOracle
