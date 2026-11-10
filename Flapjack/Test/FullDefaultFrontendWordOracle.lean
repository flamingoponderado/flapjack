-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang
import Flapjack.Test.CakeWordOracleHelpers

namespace Flapjack.Test.FullDefaultFrontendWordOracle

open Flapjack.Test.CakeWordOracleHelpers

private def matches_fragment73 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 40)) ((.seq .skip ((.seq ((.assign 1 ((.const 40)))) ((.seq ((.alloc 1 (live94, live95))) .skip)))))) .skip)))) ((.seq ((.assign 68 ((.load ((.op .add [(.lookup .globReal), (.const 16)])))))) ((.seq ((.assign 70 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 68)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 66)) (.const 1))])])))))) ((.seq ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 3 ((.const 1125899906843123)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 70)) ((.seq ((.store ((.op .add [(.var 1), (.const 16)])) 10)) ((.seq ((.store ((.op .add [(.var 1), (.const 24)])) 4)) ((.seq ((.store ((.op .add [(.var 1), (.const 32)])) 2)) .skip)))))))))) ((.seq ((.assign 72 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 15)])))) ((.set .nextFree ((.op .add [(.var 1), (.const 40)])))))))))))) ((.return 0 [72])))))))))) =>
      decide (live94 = Flapjack.sptListInsert [0] .ln) &&
      decide (live95 = Flapjack.sptListInsert [2, 4, 10, 66] .ln)
  | _ => false

private def matches_fragment74 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 60 56 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 60), (.var 56)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live86, live87), .skip, 72, 6))) ((some 13)) [60, 56] none)))))) ((.move 2 [(62, 1)])))))))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 62)) (.const 1))))) ((.seq ((.inst ((.arith ((.longMul 3 1 1 56)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.op .and [(.const 1), (.op .or [(.var 62), (.var 56)])])])))) ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 1))))) ((.seq ((.ite .equal 3 ((.imm 0)) .skip ((.mustTerminate ((.call ((some ([1], (live88, live89), .skip, 72, 7))) ((some 15)) [62, 56] none)))))) ((.move 2 [(64, 1)])))))))))))) ((.seq ((.seq ((.assign 1 ((.op .or [(.var 64), (.var 58)])))) ((.seq ((.assign 1 ((.op .or [(.var 1), (.shift .lsr ((.var 1)) (.const 63))])))) ((.ite .test 1 ((.imm 1)) ((.seq ((.assign 1 ((.const 0)))) ((.seq ((.mustTerminate ((.call ((some ([1], (live90, live91), .skip, 72, 9))) ((some 23)) [1, 64, 58] none)))) ((.assign 66 ((.shift .lsl ((.var 1)) (.const 2))))))))) ((.seq ((.mustTerminate ((.call ((some ([1], (live92, live93), .skip, 72, 8))) ((some 16)) [64, 58] none)))) ((.move 2 [(66, 1)])))))))))) fragment73)))))) =>
      decide (live86 = Flapjack.sptListInsert [0] .ln) &&
      decide (live87 = Flapjack.sptListInsert [2, 4, 10, 56, 58] .ln) &&
      decide (live88 = Flapjack.sptListInsert [0] .ln) &&
      decide (live89 = Flapjack.sptListInsert [2, 4, 10, 58] .ln) &&
      decide (live90 = Flapjack.sptListInsert [0] .ln) &&
      decide (live91 = Flapjack.sptListInsert [2, 4, 10] .ln) &&
      decide (live92 = Flapjack.sptListInsert [0] .ln) &&
      decide (live93 = Flapjack.sptListInsert [2, 4, 10] .ln) &&
      matches_fragment73 fragment73
  | _ => false

private def matches_fragment75 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 5)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 102)) ((.seq ((.store ((.op .add [(.var 1), (.const 16)])) 10)) ((.seq ((.store ((.op .add [(.var 1), (.const 24)])) 80)) ((.seq ((.store ((.op .add [(.var 1), (.const 32)])) 2)) .skip)))))))))) ((.seq ((.seq ((.assign 3 ((.op .or [(.const 1), (.shift .lsl ((.op .sub [(.lookup .nextFree), (.lookup .currHeap)])) (.const 5))])))) ((.seq ((.ite .lower 9 ((.imm 1)) ((.assign 3 ((.op .or [(.var 3), (.shift .lsl ((.var 9)) (.const 3))])))) ((.assign 3 ((.op .or [(.var 3), (.const 8)])))))) ((.ite .lower 7 ((.imm 3)) ((.assign 3 ((.op .or [(.var 3), (.shift .lsl ((.var 7)) (.const 1))])))) ((.assign 3 ((.op .or [(.var 3), (.const 6)])))))))))) ((.seq ((.set .nextFree ((.op .add [(.var 1), (.const 8), (.shift .lsl ((.var 7)) (.const 3))])))) ((.seq ((.assign 15 ((.var 78)))) ((.seq ((.assign 13 ((.op .add [(.var 1), (.const 40)])))) ((.seq ((.assign 11 ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 8), (.shift .lsl ((.var 108)) (.const 1))])))) ((.ite .test 15 ((.reg 15)) ((.assign 110 ((.var 3)))) ((.mustTerminate ((.call ((some ([110], (live117, .ln), .skip, 72, 19))) ((some 24)) [15, 11, 13, 3] none)))))))))))))))))) =>
      decide (live117 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment76 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 104 78 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 104), (.var 78)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live112, live113), .skip, 72, 18))) ((some 13)) [104, 78] none)))))) ((.move 2 [(106, 1)])))))))) ((.seq ((.assign 108 ((.const 12)))) ((.seq ((.seq ((.ite .test 106 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live114, .ln))))))) ((.seq ((.assign 1 ((.var 106)))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live115, live116))) .skip)))) .skip)))))))) ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 5 ((.op .or [(.shift .lsl ((.var 106)) (.const 46)), (.const 499)])))) ((.seq ((.assign 7 ((.shift .lsr ((.var 106)) (.const 2))))) ((.seq ((.assign 9 ((.const 31)))) fragment75)))))))))))))) ((.return 0 [110])))))))) =>
      decide (live112 = Flapjack.sptListInsert [0] .ln) &&
      decide (live113 = Flapjack.sptListInsert [2, 4, 10, 78, 80, 102] .ln) &&
      decide (live114 = Flapjack.sptListInsert [0] .ln) &&
      decide (live115 = Flapjack.sptListInsert [0] .ln) &&
      decide (live116 = Flapjack.sptListInsert [2, 4, 10, 78, 80, 102, 106, 108] .ln) &&
      matches_fragment75 fragment75
  | _ => false

private def matches_fragment77 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 1 ((.op .or [(.var 94), (.var 88)])))) ((.seq ((.assign 1 ((.op .or [(.var 1), (.shift .lsr ((.var 1)) (.const 63))])))) ((.ite .test 1 ((.imm 1)) ((.seq ((.assign 1 ((.const 0)))) ((.seq ((.mustTerminate ((.call ((some ([1], (live106, live107), .skip, 72, 16))) ((some 23)) [1, 94, 88] none)))) ((.assign 96 ((.shift .lsl ((.var 1)) (.const 2))))))))) ((.seq ((.mustTerminate ((.call ((some ([1], (live108, live109), .skip, 72, 15))) ((some 16)) [94, 88] none)))) ((.move 2 [(96, 1)])))))))))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 96 78 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 96), (.var 78)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live110, live111), .skip, 72, 17))) ((some 13)) [96, 78] none)))))) ((.move 2 [(98, 1)])))))))) ((.seq ((.assign 100 ((.load ((.op .add [(.lookup .globReal), (.const 16)])))))) ((.seq ((.assign 102 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 100)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 98)) (.const 1))])])))))) ((.seq ((.assign 104 ((.const 16)))) fragment76)))))))))) =>
      decide (live106 = Flapjack.sptListInsert [0] .ln) &&
      decide (live107 = Flapjack.sptListInsert [2, 4, 10, 78, 80] .ln) &&
      decide (live108 = Flapjack.sptListInsert [0] .ln) &&
      decide (live109 = Flapjack.sptListInsert [2, 4, 10, 78, 80] .ln) &&
      decide (live110 = Flapjack.sptListInsert [0] .ln) &&
      decide (live111 = Flapjack.sptListInsert [2, 4, 10, 78, 80] .ln) &&
      matches_fragment76 fragment76
  | _ => false

private def matches_fragment78 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 84 78 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 84), (.var 78)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live100, live101), .skip, 72, 12))) ((some 13)) [84, 78] none)))))) ((.move 2 [(86, 1)])))))))) ((.seq ((.assign 88 ((.const 8)))) ((.seq ((.assign 90 ((.const 18446744073709551612)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 90 86 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 90), (.var 86)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live102, live103), .skip, 72, 13))) ((some 13)) [90, 86] none)))))) ((.move 2 [(92, 1)])))))))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 92)) (.const 1))))) ((.seq ((.inst ((.arith ((.longMul 3 1 1 86)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.op .and [(.const 1), (.op .or [(.var 92), (.var 86)])])])))) ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 1))))) ((.seq ((.ite .equal 3 ((.imm 0)) .skip ((.mustTerminate ((.call ((some ([1], (live104, live105), .skip, 72, 14))) ((some 15)) [92, 86] none)))))) ((.move 2 [(94, 1)])))))))))))) fragment77)))))))))) =>
      decide (live100 = Flapjack.sptListInsert [0] .ln) &&
      decide (live101 = Flapjack.sptListInsert [2, 4, 10, 78, 80] .ln) &&
      decide (live102 = Flapjack.sptListInsert [0] .ln) &&
      decide (live103 = Flapjack.sptListInsert [2, 4, 10, 78, 80, 86, 88] .ln) &&
      decide (live104 = Flapjack.sptListInsert [0] .ln) &&
      decide (live105 = Flapjack.sptListInsert [2, 4, 10, 78, 80, 88] .ln) &&
      matches_fragment77 fragment77
  | _ => false

private def matches_fragment79 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 54 ((.imm 18)) ((.seq ((.assign 56 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 16)])))))) ((.seq ((.assign 58 ((.const 8)))) ((.seq ((.assign 60 ((.const 18446744073709551612)))) fragment74)))))) ((.seq ((.ite .test 4 ((.imm 1)) ((.assign 74 ((.const 0)))) ((.assign 74 ((.shift .lsl ((.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) (.const 48))) (.const 2))))))) ((.seq ((.assign 76 ((.const 18446744073709551604)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 76 74 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 76), (.var 74)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live96, live97), .skip, 72, 10))) ((some 13)) [76, 74] none)))))) ((.move 2 [(78, 1)])))))))) ((.seq ((.assign 80 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 24)])))))) ((.seq ((.assign 82 ((.const 4)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 82 10 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 82), (.var 10)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live98, live99), .skip, 72, 11))) ((some 13)) [82, 10] none)))))) ((.move 2 [(84, 1)])))))))) fragment78)))))))))))))) =>
      decide (live96 = Flapjack.sptListInsert [0] .ln) &&
      decide (live97 = Flapjack.sptListInsert [2, 4, 10] .ln) &&
      decide (live98 = Flapjack.sptListInsert [0] .ln) &&
      decide (live99 = Flapjack.sptListInsert [2, 4, 10, 78, 80] .ln) &&
      matches_fragment74 fragment74 &&
      matches_fragment78 fragment78
  | _ => false

private def matches_fragment80 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.assign 12 ((.const 0)))) ((.seq ((.seq ((.assign 1 ((.var 10)))) ((.seq ((.assign 3 ((.var 12)))) ((.seq ((.assign 5 ((.op .or [(.var 1), (.var 3)])))) ((.seq ((.ite .test 5 ((.imm 1)) .skip ((.seq ((.mustTerminate ((.call ((some ([1], (live82, live83), .skip, 72, 3))) ((some 19)) [1, 3] none)))) ((.assign 3 ((.const 1)))))))) ((.ite .less 1 ((.reg 3)) ((.assign 14 (.const 18))) ((.assign 14 (.const 2))))))))))))) ((.ite .equal 14 ((.imm 18)) ((.seq ((.assign 16 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 16)])))))) ((.seq ((.ite .less 16 ((.imm 4)) ((.assign 18 (.const 18))) ((.assign 18 (.const 2))))) fragment72)))) ((.seq ((.seq ((.assign 1 ((.var 4)))) ((.seq ((.ite .test 4 ((.imm 1)) .skip ((.assign 1 ((.op .and [(.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]))), (.const 281474976710654)])))))) ((.ite .equal 1 ((.imm 482)) ((.assign 54 (.const 18))) ((.assign 54 (.const 2))))))))) fragment79)))))))) =>
      decide (live82 = Flapjack.sptListInsert [0] .ln) &&
      decide (live83 = Flapjack.sptListInsert [2, 4, 10] .ln) &&
      shared_matches_fragment72 fragment72 &&
      matches_fragment79 fragment79
  | _ => false

private def matches_fragment81 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 20 ((.imm 18)) ((.seq ((.assign 22 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.const 8)])))))) ((.seq ((.call ((some ([24], (live122, live123), .skip, 76, 4))) none [4, 6, 22] none)) ((.seq ((.assign 26 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 24)) (.const 5))]), (.const 16)])))))) ((.seq ((.ite .equal 26 ((.imm 0)) ((.assign 28 (.const 18))) ((.assign 28 (.const 2))))) ((.ite .equal 28 ((.imm 18)) ((.seq ((.assign 30 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 24)) (.const 5))]), (.const 8)])))))) ((.call none none [0, 2, 24, 30] none)))) ((.call none ((some 72)) [0, 2, 24] none)))))))))))) ((.seq ((.assign 38 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.const 8)])))))) ((.seq ((.call ((some ([40], (live124, .ln), .skip, 76, 5))) none [2, 4, 6, 38] none)) ((.seq ((.assign 42 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 40)) (.const 5))]), (.const 16)])))))) ((.seq ((.ite .equal 42 ((.imm 0)) ((.assign 44 (.const 18))) ((.assign 44 (.const 2))))) ((.ite .equal 44 ((.imm 18)) ((.seq ((.assign 46 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 40)) (.const 5))]), (.const 8)])))))) ((.call none none [0, 40, 46] none)))) ((.call none ((some 72)) [0, 40] none)))))))))))))) =>
      decide (live122 = Flapjack.sptListInsert [0] .ln) &&
      decide (live123 = Flapjack.sptListInsert [2] .ln) &&
      decide (live124 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment82 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 48)) ((.seq .skip ((.seq ((.assign 1 ((.const 48)))) ((.seq ((.alloc 1 (live135, live136))) .skip)))))) .skip)))) ((.seq ((.assign 74 ((.load ((.op .add [(.lookup .globReal), (.const 16)])))))) ((.seq ((.assign 76 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 74)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 72)) (.const 1))])])))))) ((.seq ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 3 ((.const 1407374883553779)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 76)) ((.seq ((.store ((.op .add [(.var 1), (.const 16)])) 12)) ((.seq ((.store ((.op .add [(.var 1), (.const 24)])) 6)) ((.seq ((.store ((.op .add [(.var 1), (.const 32)])) 2)) ((.seq ((.store ((.op .add [(.var 1), (.const 40)])) 4)) .skip)))))))))))) ((.seq ((.assign 78 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 15)])))) ((.set .nextFree ((.op .add [(.var 1), (.const 48)])))))))))))) ((.return 0 [78])))))))))) =>
      decide (live135 = Flapjack.sptListInsert [0] .ln) &&
      decide (live136 = Flapjack.sptListInsert [2, 4, 6, 12, 72] .ln)
  | _ => false

private def matches_fragment83 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 64)) (.const 1))))) ((.seq ((.inst ((.arith ((.longMul 3 1 1 58)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.op .and [(.const 1), (.op .or [(.var 64), (.var 58)])])])))) ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 1))))) ((.seq ((.ite .equal 3 ((.imm 0)) .skip ((.mustTerminate ((.call ((some ([1], (live127, live128), .skip, 76, 7))) ((some 15)) [64, 58] none)))))) ((.move 2 [(66, 1)])))))))))))) ((.seq ((.seq ((.assign 1 ((.op .or [(.var 66), (.var 60)])))) ((.seq ((.assign 1 ((.op .or [(.var 1), (.shift .lsr ((.var 1)) (.const 63))])))) ((.ite .test 1 ((.imm 1)) ((.seq ((.assign 1 ((.const 0)))) ((.seq ((.mustTerminate ((.call ((some ([1], (live129, live130), .skip, 76, 9))) ((some 23)) [1, 66, 60] none)))) ((.assign 68 ((.shift .lsl ((.var 1)) (.const 2))))))))) ((.seq ((.mustTerminate ((.call ((some ([1], (live131, live132), .skip, 76, 8))) ((some 16)) [66, 60] none)))) ((.move 2 [(68, 1)])))))))))) ((.seq ((.assign 70 ((.const 4)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 70 68 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 70), (.var 68)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live133, live134), .skip, 76, 10))) ((some 13)) [70, 68] none)))))) ((.move 2 [(72, 1)])))))))) fragment82)))))))) =>
      decide (live127 = Flapjack.sptListInsert [0] .ln) &&
      decide (live128 = Flapjack.sptListInsert [2, 4, 6, 12, 60] .ln) &&
      decide (live129 = Flapjack.sptListInsert [0] .ln) &&
      decide (live130 = Flapjack.sptListInsert [2, 4, 6, 12] .ln) &&
      decide (live131 = Flapjack.sptListInsert [0] .ln) &&
      decide (live132 = Flapjack.sptListInsert [2, 4, 6, 12] .ln) &&
      decide (live133 = Flapjack.sptListInsert [0] .ln) &&
      decide (live134 = Flapjack.sptListInsert [2, 4, 6, 12] .ln) &&
      matches_fragment82 fragment82
  | _ => false

private def matches_fragment84 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 5)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 112)) ((.seq ((.store ((.op .add [(.var 1), (.const 16)])) 12)) ((.seq ((.store ((.op .add [(.var 1), (.const 24)])) 86)) ((.seq ((.store ((.op .add [(.var 1), (.const 32)])) 2)) ((.seq ((.store ((.op .add [(.var 1), (.const 40)])) 4)) .skip)))))))))))) ((.seq ((.seq ((.assign 3 ((.op .or [(.const 1), (.shift .lsl ((.op .sub [(.lookup .nextFree), (.lookup .currHeap)])) (.const 5))])))) ((.seq ((.ite .lower 9 ((.imm 1)) ((.assign 3 ((.op .or [(.var 3), (.shift .lsl ((.var 9)) (.const 3))])))) ((.assign 3 ((.op .or [(.var 3), (.const 8)])))))) ((.ite .lower 7 ((.imm 3)) ((.assign 3 ((.op .or [(.var 3), (.shift .lsl ((.var 7)) (.const 1))])))) ((.assign 3 ((.op .or [(.var 3), (.const 6)])))))))))) ((.seq ((.set .nextFree ((.op .add [(.var 1), (.const 8), (.shift .lsl ((.var 7)) (.const 3))])))) ((.seq ((.assign 15 ((.var 84)))) ((.seq ((.assign 13 ((.op .add [(.var 1), (.const 48)])))) ((.seq ((.assign 11 ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.const 8), (.shift .lsl ((.var 118)) (.const 1))])))) ((.ite .test 15 ((.reg 15)) ((.assign 120 ((.var 3)))) ((.mustTerminate ((.call ((some ([120], (live160, .ln), .skip, 76, 21))) ((some 24)) [15, 11, 13, 3] none)))))))))))))))))) =>
      decide (live160 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment85 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 114 84 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 114), (.var 84)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live155, live156), .skip, 76, 20))) ((some 13)) [114, 84] none)))))) ((.move 2 [(116, 1)])))))))) ((.seq ((.assign 118 ((.const 12)))) ((.seq ((.seq ((.ite .test 116 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live157, .ln))))))) ((.seq ((.assign 1 ((.var 116)))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live158, live159))) .skip)))) .skip)))))))) ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 5 ((.op .or [(.shift .lsl ((.var 116)) (.const 46)), (.const 499)])))) ((.seq ((.assign 7 ((.shift .lsr ((.var 116)) (.const 2))))) ((.seq ((.assign 9 ((.const 31)))) fragment84)))))))))))))) ((.return 0 [120])))))))) =>
      decide (live155 = Flapjack.sptListInsert [0] .ln) &&
      decide (live156 = Flapjack.sptListInsert [2, 4, 6, 12, 84, 86, 112] .ln) &&
      decide (live157 = Flapjack.sptListInsert [0] .ln) &&
      decide (live158 = Flapjack.sptListInsert [0] .ln) &&
      decide (live159 = Flapjack.sptListInsert [2, 4, 6, 12, 84, 86, 112, 116, 118] .ln) &&
      matches_fragment84 fragment84
  | _ => false

private def matches_fragment86 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 1 ((.op .or [(.var 104), (.var 98)])))) ((.seq ((.assign 1 ((.op .or [(.var 1), (.shift .lsr ((.var 1)) (.const 63))])))) ((.ite .test 1 ((.imm 1)) ((.seq ((.assign 1 ((.const 0)))) ((.seq ((.mustTerminate ((.call ((some ([1], (live149, live150), .skip, 76, 18))) ((some 23)) [1, 104, 98] none)))) ((.assign 106 ((.shift .lsl ((.var 1)) (.const 2))))))))) ((.seq ((.mustTerminate ((.call ((some ([1], (live151, live152), .skip, 76, 17))) ((some 16)) [104, 98] none)))) ((.move 2 [(106, 1)])))))))))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 106 96 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 106), (.var 96)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live153, live154), .skip, 76, 19))) ((some 13)) [106, 96] none)))))) ((.move 2 [(108, 1)])))))))) ((.seq ((.assign 110 ((.load ((.op .add [(.lookup .globReal), (.const 16)])))))) ((.seq ((.assign 112 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 110)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 108)) (.const 1))])])))))) ((.seq ((.assign 114 ((.const 20)))) fragment85)))))))))) =>
      decide (live149 = Flapjack.sptListInsert [0] .ln) &&
      decide (live150 = Flapjack.sptListInsert [2, 4, 6, 12, 84, 86, 96] .ln) &&
      decide (live151 = Flapjack.sptListInsert [0] .ln) &&
      decide (live152 = Flapjack.sptListInsert [2, 4, 6, 12, 84, 86, 96] .ln) &&
      decide (live153 = Flapjack.sptListInsert [0] .ln) &&
      decide (live154 = Flapjack.sptListInsert [2, 4, 6, 12, 84, 86] .ln) &&
      matches_fragment85 fragment85
  | _ => false

private def matches_fragment87 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 94 84 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 94), (.var 84)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live143, live144), .skip, 76, 14))) ((some 13)) [94, 84] none)))))) ((.move 2 [(96, 1)])))))))) ((.seq ((.assign 98 ((.const 8)))) ((.seq ((.assign 100 ((.const 18446744073709551612)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 100 92 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 100), (.var 92)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live145, live146), .skip, 76, 15))) ((some 13)) [100, 92] none)))))) ((.move 2 [(102, 1)])))))))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 102)) (.const 1))))) ((.seq ((.inst ((.arith ((.longMul 3 1 1 92)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.op .and [(.const 1), (.op .or [(.var 102), (.var 92)])])])))) ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 1))))) ((.seq ((.ite .equal 3 ((.imm 0)) .skip ((.mustTerminate ((.call ((some ([1], (live147, live148), .skip, 76, 16))) ((some 15)) [102, 92] none)))))) ((.move 2 [(104, 1)])))))))))))) fragment86)))))))))) =>
      decide (live143 = Flapjack.sptListInsert [0] .ln) &&
      decide (live144 = Flapjack.sptListInsert [2, 4, 6, 12, 84, 86, 92] .ln) &&
      decide (live145 = Flapjack.sptListInsert [0] .ln) &&
      decide (live146 = Flapjack.sptListInsert [2, 4, 6, 12, 84, 86, 92, 96, 98] .ln) &&
      decide (live147 = Flapjack.sptListInsert [0] .ln) &&
      decide (live148 = Flapjack.sptListInsert [2, 4, 6, 12, 84, 86, 96, 98] .ln) &&
      matches_fragment86 fragment86
  | _ => false

private def matches_fragment88 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 82 80 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 82), (.var 80)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live137, live138), .skip, 76, 11))) ((some 13)) [82, 80] none)))))) ((.move 2 [(84, 1)])))))))) ((.seq ((.assign 86 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.const 24)])))))) ((.seq ((.assign 88 ((.const 8)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 88 12 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 88), (.var 12)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live139, live140), .skip, 76, 12))) ((some 13)) [88, 12] none)))))) ((.move 2 [(90, 1)])))))))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 90 84 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 90), (.var 84)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live141, live142), .skip, 76, 13))) ((some 13)) [90, 84] none)))))) ((.move 2 [(92, 1)])))))))) ((.seq ((.assign 94 ((.const 4)))) fragment87)))))))))))) =>
      decide (live137 = Flapjack.sptListInsert [0] .ln) &&
      decide (live138 = Flapjack.sptListInsert [2, 4, 6, 12] .ln) &&
      decide (live139 = Flapjack.sptListInsert [0] .ln) &&
      decide (live140 = Flapjack.sptListInsert [2, 4, 6, 12, 84, 86] .ln) &&
      decide (live141 = Flapjack.sptListInsert [0] .ln) &&
      decide (live142 = Flapjack.sptListInsert [2, 4, 6, 12, 84, 86] .ln) &&
      matches_fragment87 fragment87
  | _ => false

private def matches_fragment89 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 16 ((.imm 18)) ((.seq ((.assign 18 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.const 16)])))))) ((.seq ((.ite .less 18 ((.imm 4)) ((.assign 20 (.const 18))) ((.assign 20 (.const 2))))) fragment81)))) ((.seq ((.seq ((.assign 1 ((.var 6)))) ((.seq ((.ite .test 6 ((.imm 1)) .skip ((.assign 1 ((.op .and [(.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]))), (.const 281474976710654)])))))) ((.ite .equal 1 ((.imm 482)) ((.assign 56 (.const 18))) ((.assign 56 (.const 2))))))))) ((.ite .equal 56 ((.imm 18)) ((.seq ((.assign 58 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.const 16)])))))) ((.seq ((.assign 60 ((.const 8)))) ((.seq ((.assign 62 ((.const 18446744073709551612)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 62 58 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 62), (.var 58)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live125, live126), .skip, 76, 6))) ((some 13)) [62, 58] none)))))) ((.move 2 [(64, 1)])))))))) fragment83)))))))) ((.seq ((.ite .test 6 ((.imm 1)) ((.assign 80 ((.const 0)))) ((.assign 80 ((.shift .lsl ((.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))])))) (.const 48))) (.const 2))))))) ((.seq ((.assign 82 ((.const 18446744073709551604)))) fragment88)))))))))) =>
      decide (live125 = Flapjack.sptListInsert [0] .ln) &&
      decide (live126 = Flapjack.sptListInsert [2, 4, 6, 12, 58, 60] .ln) &&
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
  | (72, 3, (.seq ((.assign 6 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 16)])))))) ((.seq ((.assign 8 ((.const 18446744073709551612)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 8 6 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 8), (.var 6)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live80, live81), .skip, 72, 2))) ((some 13)) [8, 6] none)))))) ((.move 2 [(10, 1)])))))))) fragment80))))), 0) =>
      decide (live80 = Flapjack.sptListInsert [0] .ln) &&
      decide (live81 = Flapjack.sptListInsert [2, 4] .ln) &&
      matches_fragment80 fragment80
  | _ => false

private def matches64 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (76, 4, (.seq ((.assign 8 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.const 16)])))))) ((.seq ((.assign 10 ((.const 18446744073709551608)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 10 8 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 10), (.var 8)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live118, live119), .skip, 76, 2))) ((some 13)) [10, 8] none)))))) ((.move 2 [(12, 1)])))))))) ((.seq ((.assign 14 ((.const 0)))) ((.seq ((.seq ((.assign 1 ((.var 12)))) ((.seq ((.assign 3 ((.var 14)))) ((.seq ((.assign 5 ((.op .or [(.var 1), (.var 3)])))) ((.seq ((.ite .test 5 ((.imm 1)) .skip ((.seq ((.mustTerminate ((.call ((some ([1], (live120, live121), .skip, 76, 3))) ((some 19)) [1, 3] none)))) ((.assign 3 ((.const 1)))))))) ((.ite .less 1 ((.reg 3)) ((.assign 16 (.const 18))) ((.assign 16 (.const 2))))))))))))) fragment89))))))))), 0) =>
      decide (live118 = Flapjack.sptListInsert [0] .ln) &&
      decide (live119 = Flapjack.sptListInsert [2, 4, 6] .ln) &&
      decide (live120 = Flapjack.sptListInsert [0] .ln) &&
      decide (live121 = Flapjack.sptListInsert [2, 4, 6, 12] .ln) &&
      matches_fragment89 fragment89
  | _ => false

private def matches66 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (84, 3, (.seq ((.assign 6 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 16)])))))) fragment90), 0) =>
      shared_matches_fragment90 fragment90
  | _ => false

private def matches67 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (88, 1, (.seq ((.assign 2 ((.const 4)))) ((.seq ((.call ((some ([4], (live165, .ln), .skip, 88, 2))) ((some 62)) [2] none)) ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 16)) ((.seq .skip ((.seq ((.assign 1 ((.const 16)))) ((.seq ((.alloc 1 (live166, .ln))) .skip)))))) .skip)))) ((.seq ((.locValue 6 80)) ((.seq ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 3 ((.const 281474976710659)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 6)) .skip)))) ((.seq ((.assign 8 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 3)])))) ((.set .nextFree ((.op .add [(.var 1), (.const 16)])))))))))))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 16)])) 8)) ((.assign 10 (.const 2))))) ((.call none ((some 92)) [0] none))))))))))))), 0) =>
      decide (live165 = Flapjack.sptListInsert [0] .ln) &&
      decide (live166 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches68 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (92, 1, (.seq ((.assign 2 ((.const 4)))) ((.seq ((.call ((some ([4], (live167, .ln), .skip, 92, 2))) ((some 62)) [2] none)) ((.seq ((.assign 6 (.const 2))) ((.seq ((.assign 8 (.const 2))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 24)])) 8)) ((.assign 10 (.const 2))))) ((.call none ((some 96)) [0] none))))))))))), 0) =>
      decide (live167 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches69 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (96, 1, (.seq ((.assign 2 ((.const 8)))) ((.seq ((.call ((some ([4], (live168, .ln), .skip, 96, 2))) ((some 62)) [2] none)) ((.seq ((.assign 6 (.const 2))) ((.call none ((some 100)) [0] none))))))), 0) =>
      decide (live168 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches70 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (100, 1, (.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 16)) ((.seq .skip ((.seq ((.assign 1 ((.const 16)))) ((.seq ((.alloc 1 (live169, .ln))) .skip)))))) .skip)))) ((.seq ((.assign 2 (.const 2))) ((.seq ((.seq ((.set .triggerGC ((.op .sub [(.lookup .triggerGC), (.const 16)])))) ((.seq ((.assign 1 ((.op .sub [(.lookup .endOfHeap), (.const 16)])))) ((.seq ((.set .endOfHeap ((.var 1)))) ((.seq ((.assign 3 ((.const 281474976710667)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 2)) .skip)))) ((.assign 4 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 1)])))))))))))))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 32)])) 4)) ((.assign 6 (.const 2))))) ((.return 0 [6]))))))))), 0) =>
      decide (live169 = Flapjack.sptListInsert [0] .ln)
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  code.length == 71 &&
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
    (match code[65]? with | some entry => shared_matches65 entry | none => false) &&
    (match code[66]? with | some entry => matches66 entry | none => false) &&
    (match code[67]? with | some entry => matches67 entry | none => false) &&
    (match code[68]? with | some entry => matches68 entry | none => false) &&
    (match code[69]? with | some entry => matches69 entry | none => false) &&
    (match code[70]? with | some entry => matches70 entry | none => false)

end Flapjack.Test.FullDefaultFrontendWordOracle
