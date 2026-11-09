-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.FullCakeWordOracle

private def matches_fragment0 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live1, live2))) .skip)))) .skip)))))))) ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 5 ((.op .or [(.shift .lsl ((.var 2)) (.const 46)), (.const 3), (.var 6)])))) ((.seq ((.assign 7 ((.shift .lsr ((.var 2)) (.const 2))))) ((.seq ((.assign 9 ((.shift .lsr ((.var 6)) (.const 4))))) ((.seq ((.seq ((.assign 3 ((.op .or [(.const 1), (.shift .lsl ((.op .sub [(.lookup .nextFree), (.lookup .currHeap)])) (.const 5))])))) ((.seq ((.ite .lower 9 ((.imm 1)) ((.assign 3 ((.op .or [(.var 3), (.shift .lsl ((.var 9)) (.const 3))])))) ((.assign 3 ((.op .or [(.var 3), (.const 8)])))))) ((.ite .lower 7 ((.imm 3)) ((.assign 3 ((.op .or [(.var 3), (.shift .lsl ((.var 7)) (.const 1))])))) ((.assign 3 ((.op .or [(.var 3), (.const 6)])))))))))) ((.call none ((some 8)) [0, 1, 4, 2, 3, 5] none)))))))))))))) =>
      decide (live1 = Flapjack.sptListInsert [0] .ln) &&
      decide (live2 = Flapjack.sptListInsert [2, 4, 6] .ln)
  | _ => false

private def matches_fragment1 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.store ((.var 9)) 5)) ((.seq ((.assign 11 ((.op .and [(.shift .lsr ((.var 2)) (.const 2)), (.const 7)])))) ((.seq ((.assign 13 ((.const 0)))) ((.seq ((.store ((.var 1)) 13)) ((.seq ((.ite .equal 11 ((.imm 0)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 0)))))) ((.ite .equal 11 ((.imm 1)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 1)))))) ((.ite .equal 11 ((.imm 2)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 2)))))) ((.ite .equal 11 ((.imm 3)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 3)))))) ((.ite .equal 11 ((.imm 4)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 4)))))) ((.ite .equal 11 ((.imm 5)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 5)))))) ((.ite .equal 11 ((.imm 6)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 6)))))) ((.ite .equal 11 ((.imm 7)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 7)))))) .skip)))))))))))))))))))))))))))))))) ((.seq ((.assign 7 ((.op .sub [(.var 7), (.const 4)])))) ((.call none ((some 11)) [0, 9, 4, 7, 3] none)))))))))))))) =>
      true
  | _ => false

private def matches_fragment2 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live4, live5))) .skip)))) .skip)))))))) ((.seq ((.assign 5 ((.shift .lsr ((.op .add [(.shift .lsr ((.var 2)) (.const 2)), (.const 8)])) (.const 3))))) ((.seq ((.assign 7 ((.shift .lsl ((.var 5)) (.const 2))))) ((.seq ((.assign 9 ((.lookup .nextFree)))) ((.seq ((.assign 1 ((.op .add [(.var 9), (.shift .lsl ((.var 5)) (.const 3))])))) ((.seq ((.set .nextFree ((.op .add [(.var 1), (.const 8)])))) ((.seq ((.assign 3 ((.op .or [(.shift .lsl ((.op .sub [(.var 9), (.lookup .currHeap)])) (.const 5)), (.const 1)])))) ((.seq ((.assign 5 ((.op .or [(.op .or [(.shift .lsl ((.op .add [(.shift .lsr ((.var 2)) (.const 2)), (.const 8)])) (.const 45)), (.const 7)]), (.var 6)])))) ((.seq ((.seq ((.assign 4 ((.shift .lsr ((.var 4)) (.const 2))))) ((.seq ((.assign 4 ((.op .or [(.var 4), (.shift .lsl ((.var 4)) (.const 8))])))) ((.seq ((.assign 4 ((.op .or [(.var 4), (.shift .lsl ((.var 4)) (.const 16))])))) ((.assign 4 ((.op .or [(.var 4), (.shift .lsl ((.var 4)) (.const 32))])))))))))) fragment1)))))))))))))))))) =>
      decide (live4 = Flapjack.sptListInsert [0] .ln) &&
      decide (live5 = Flapjack.sptListInsert [2, 4, 6] .ln) &&
      matches_fragment1 fragment1
  | _ => false

private def matches_fragment3 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.ite .equal 1 ((.imm 2)) ((.seq ((.assign 5 ((.shift .lsr ((.var 3)) (.const 61))))) ((.ite .test 5 ((.reg 5)) ((.seq ((.assign 1 ((.shift .lsl ((.var 3)) (.const 2))))) ((.return 0 [1])))) .skip)))) ((.ite .equal 1 ((.imm 3)) ((.seq ((.assign 5 ((.shift .lsr ((.op .sub [(.var 3), (.const 1)])) (.const 61))))) ((.ite .test 5 ((.reg 5)) ((.seq ((.assign 1 ((.op .sub [(.const 0), (.shift .lsl ((.var 3)) (.const 2))])))) ((.return 0 [1])))) .skip)))) ((.assign 5 ((.const 0)))))))) ((.seq ((.assign 5 ((.lookup .nextFree)))) ((.seq ((.assign 6 ((.shift .lsr ((.var 1)) (.const 1))))) ((.seq ((.assign 8 ((.op .and [(.var 1), (.const 1)])))) ((.seq ((.assign 7 ((.op .or [(.const 15), (.shift .lsl ((.var 6)) (.const 48)), (.shift .lsl ((.var 8)) (.const 4))])))) ((.seq ((.store ((.var 5)) 7)) ((.seq ((.assign 1 ((.op .sub [(.var 5), (.lookup .currHeap)])))) ((.seq ((.assign 1 ((.op .or [(.shift .lsl ((.var 1)) (.const 5)), (.const 1)])))) ((.seq ((.set .nextFree ((.op .add [(.var 5), (.const 8), (.shift .lsl ((.var 6)) (.const 3))])))) ((.return 0 [1])))))))))))))))))))) =>
      true
  | _ => false

private def matches_fragment4 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 4 ((.imm 0)) ((.seq ((.assign 7 ((.const 0)))) ((.seq ((.set ((.temp 1)) ((.var 4)))) ((.seq ((.set ((.temp 30)) ((.var 4)))) ((.set ((.temp 11)) ((.var 4)))))))))) ((.ite .notTest 4 ((.imm 1)) ((.seq ((.assign 7 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.set ((.temp 30)) ((.op .add [(.var 7), (.const 8)])))) ((.seq ((.set ((.temp 1)) ((.op .add [(.shift .lsl ((.shift .lsr ((.load ((.var 7)))) (.const 48))) (.const 1)), (.op .and [(.const 1), (.shift .lsr ((.load ((.var 7)))) (.const 4))])])))) ((.set ((.temp 11)) ((.const 0)))))))))) ((.ite .notLess 4 ((.imm 0)) ((.seq ((.set ((.temp 1)) (.const 2))) ((.seq ((.set ((.temp 30)) ((.lookup .otherHeap)))) ((.seq ((.set ((.temp 11)) ((.shift .lsr ((.var 4)) (.const 2))))) ((.assign 7 ((.const 0)))))))))) ((.seq ((.set ((.temp 1)) ((.const 3)))) ((.seq ((.set ((.temp 30)) ((.lookup .otherHeap)))) ((.seq ((.set ((.temp 11)) ((.op .sub [(.const 0), (.shift .asr ((.var 4)) (.const 2))])))) ((.assign 7 ((.const 0)))))))))))))))) =>
      true
  | _ => false

private def matches_fragment5 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 2 ((.imm 0)) ((.seq ((.assign 7 ((.const 0)))) ((.seq ((.set ((.temp 0)) ((.var 2)))) ((.seq ((.set ((.temp 31)) ((.var 2)))) ((.set ((.temp 12)) ((.var 2)))))))))) ((.ite .notTest 2 ((.imm 1)) ((.seq ((.assign 7 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.set ((.temp 31)) ((.op .add [(.var 7), (.const 8)])))) ((.seq ((.set ((.temp 0)) ((.op .add [(.shift .lsl ((.shift .lsr ((.load ((.var 7)))) (.const 48))) (.const 1)), (.op .and [(.const 1), (.shift .lsr ((.load ((.var 7)))) (.const 4))])])))) ((.set ((.temp 12)) ((.const 0)))))))))) ((.ite .notLess 2 ((.imm 0)) ((.seq ((.set ((.temp 0)) (.const 2))) ((.seq ((.set ((.temp 31)) ((.lookup .nextFree)))) ((.seq ((.set ((.temp 12)) ((.shift .lsr ((.var 2)) (.const 2))))) ((.assign 7 ((.const 0)))))))))) ((.seq ((.set ((.temp 0)) ((.const 3)))) ((.seq ((.set ((.temp 31)) ((.lookup .nextFree)))) ((.seq ((.set ((.temp 12)) ((.op .sub [(.const 0), (.shift .asr ((.var 2)) (.const 2))])))) ((.assign 7 ((.const 0)))))))))))))))) =>
      true
  | _ => false

private def matches_fragment6 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live6, live7))) .skip)))) .skip)))))))) ((.seq fragment5 ((.seq fragment4 ((.seq ((.get 1 ((.temp 11)))) ((.seq ((.store ((.lookup .otherHeap)) 1)) ((.seq ((.get 1 ((.temp 12)))) ((.seq ((.store ((.lookup .nextFree)) 1)) ((.seq ((.get 1 ((.temp 29)))) ((.seq ((.assign 2 ((.lookup .nextFree)))) ((.seq ((.set ((.temp 29)) ((.var 2)))) ((.seq ((.set ((.temp 3)) ((.shift .lsr ((.var 6)) (.const 2))))) ((.seq ((.assign 3 ((.const 0)))) ((.seq ((.call ((some ([0], (live8, .ln), .skip, 12, 2))) ((some 11)) [2, 3, 1, 0] none)) ((.seq ((.set ((.temp 29)) ((.op .add [(.lookup ((.temp 29))), (.const 8)])))) ((.seq ((.call ((some ([1], (live9, .ln), .skip, 12, 3))) ((some 39)) [] none)) ((.seq ((.get 1 ((.temp 10)))) ((.seq ((.ite .test 1 ((.reg 1)) ((.return 0 [1])) .skip)) ((.seq ((.assign 3 ((.load ((.op .add [(.lookup .nextFree), (.const 8)])))))) fragment3)))))))))))))))))))))))))))))))))))) =>
      decide (live6 = Flapjack.sptListInsert [0] .ln) &&
      decide (live7 = Flapjack.sptListInsert [2, 4, 6] .ln) &&
      decide (live8 = Flapjack.sptListInsert [0] .ln) &&
      decide (live9 = Flapjack.sptListInsert [0] .ln) &&
      matches_fragment5 fragment5 &&
      matches_fragment4 fragment4 &&
      matches_fragment3 fragment3
  | _ => false

private def matches_fragment7 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.assign 13 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 3 ((.load ((.var 13)))))) ((.seq ((.assign 6 ((.shift .lsr ((.var 1)) (.const 48))))) ((.seq ((.assign 8 ((.shift .lsr ((.var 3)) (.const 48))))) ((.ite .equal 1 ((.reg 3)) ((.seq ((.assign 2 ((.op .add [(.var 11), (.shift .lsl ((.var 6)) (.const 3))])))) ((.seq ((.assign 4 ((.op .add [(.var 13), (.shift .lsl ((.var 6)) (.const 3))])))) ((.ite .test 1 ((.imm 16)) ((.call none ((some 18)) [0, 6, 2, 4] none)) ((.call none ((some 18)) [0, 6, 4, 2] none)))))))) ((.ite .test 1 ((.imm 16)) ((.ite .test 3 ((.imm 16)) ((.ite .lower 6 ((.reg 8)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))))) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))))) ((.ite .test 3 ((.imm 16)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) ((.ite .lower 6 ((.reg 8)) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))))))))))))))))))) =>
      true
  | _ => false

private def matches_fragment8 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.ite .test 21 ((.imm 12)) ((.seq ((.assign 1 ((.op .and [(.var 21), (.const 281474976710654)])))) ((.seq ((.ite .equal 1 ((.imm 482)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) .skip)) ((.seq ((.ite .equal 1 ((.imm 498)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) .skip)) ((.seq ((.ite .equal 21 ((.reg 41)) .skip ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))))) ((.seq ((.assign 6 ((.shift .lsr ((.var 21)) (.const 48))))) ((.seq ((.assign 20 ((.op .add [(.var 20), (.const 8)])))) ((.seq ((.assign 40 ((.op .add [(.var 40), (.const 8)])))) ((.call none ((some 20)) [0, 6, 20, 40] none)))))))))))))))) .skip)) ((.seq ((.ite .equal 21 ((.reg 41)) .skip ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))))) ((.seq ((.ite .test 21 ((.imm 4)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 1 ((.op .and [(.var 21), (.const 24)])))) ((.seq ((.ite .equal 1 ((.imm 16)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 6 ((.shift .lsr ((.var 21)) (.const 48))))) ((.seq ((.assign 2 ((.op .add [(.var 20), (.shift .lsl ((.var 6)) (.const 3))])))) ((.seq ((.assign 4 ((.op .add [(.var 40), (.shift .lsl ((.var 6)) (.const 3))])))) ((.call none ((some 18)) [0, 6, 2, 4] none)))))))))))))))))) =>
      true
  | _ => false

private def matches_fragment9 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 24 ((.op .add [(.lookup ((.temp 2))), (.const 1)])))) ((.set ((.temp 2)) ((.var 24)))))) ((.seq ((.seq ((.assign 25 ((.const 0)))) ((.set ((.temp 3)) ((.var 25)))))) ((.seq ((.call ((some ([26], (live14, .ln), .skip, 39, 2))) ((some 40)) [] none)) ((.seq ((.seq ((.assign 27 ((.lookup ((.temp 2)))))) ((.set ((.temp 1)) ((.var 27)))))) ((.seq ((.seq ((.assign 28 ((.const 0)))) ((.set ((.temp 9)) ((.var 28)))))) ((.seq ((.call ((some ([29], (live15, .ln), .skip, 39, 3))) ((some 41)) [] none)) ((.seq ((.assign 34 ((.lookup ((.temp 3)))))) ((.ite .equal 34 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 30 ((.const 1)))) ((.set ((.temp 8)) ((.var 30)))))) ((.seq ((.seq ((.assign 31 ((.lookup ((.temp 8)))))) ((.seq ((.assign 32 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 32)) 31)))))) ((.seq ((.seq ((.assign 33 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 33)))))) ((.seq .skip .skip)))))))))))))))))))))))) =>
      decide (live14 = Flapjack.sptListInsert [0] .ln) &&
      decide (live15 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment10 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 20 ((.lookup ((.temp 8)))))) ((.set ((.temp 9)) ((.var 20)))))) ((.seq ((.seq ((.assign 21 ((.lookup ((.temp 8)))))) ((.set ((.temp 10)) ((.var 21)))))) ((.seq ((.seq ((.seq ((.assign 22 ((.op .sub [(.lookup ((.temp 2))), (.lookup ((.temp 1)))])))) ((.set ((.temp 2)) ((.var 22)))))) ((.seq ((.seq ((.seq ((.assign 23 ((.op .add [(.lookup ((.temp 1))), (.const 1)])))) ((.set ((.temp 1)) ((.var 23)))))) fragment9)) ((.seq .skip .skip)))))) ((.seq ((.seq ((.assign 36 ((.lookup ((.temp 0)))))) ((.ite .equal 36 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 35 ((.lookup ((.temp 31)))))) ((.seq ((.set ((.temp 31)) ((.lookup ((.temp 30)))))) ((.set ((.temp 30)) ((.var 35)))))))) ((.seq .skip .skip)))))))) ((.seq ((.seq ((.assign 37 ((.shift .lsl ((.lookup ((.temp 10)))) (.const 1))))) ((.set ((.temp 10)) ((.var 37)))))) ((.seq ((.seq ((.assign 38 ((.op .add [(.lookup ((.temp 10))), (.lookup ((.temp 11)))])))) ((.set ((.temp 10)) ((.var 38)))))) ((.seq .skip .skip)))))))))))))) =>
      matches_fragment9 fragment9
  | _ => false

private def matches_fragment11 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 64 ((.op .sub [(.lookup ((.temp 2))), (.lookup ((.temp 1)))])))) ((.set ((.temp 2)) ((.var 64)))))) ((.seq ((.seq ((.seq ((.assign 65 ((.op .add [(.lookup ((.temp 1))), (.const 1)])))) ((.set ((.temp 1)) ((.var 65)))))) ((.seq ((.seq ((.assign 66 ((.op .add [(.lookup ((.temp 2))), (.const 1)])))) ((.set ((.temp 2)) ((.var 66)))))) ((.seq ((.seq ((.assign 67 ((.const 1)))) ((.set ((.temp 3)) ((.var 67)))))) ((.seq ((.seq ((.assign 68 ((.op .sub [(.lookup ((.temp 8))), (.const 0)])))) ((.set ((.temp 8)) ((.var 68)))))) ((.seq ((.call ((some ([69], (live17, .ln), .skip, 39, 5))) ((some 43)) [] none)) ((.seq ((.seq ((.assign 70 ((.lookup ((.temp 2)))))) ((.set ((.temp 1)) ((.var 70)))))) ((.seq ((.seq ((.assign 71 ((.const 0)))) ((.set ((.temp 9)) ((.var 71)))))) ((.seq ((.call ((some ([72], (live18, .ln), .skip, 39, 6))) ((some 44)) [] none)) ((.seq .skip .skip)))))))))))))))))) ((.seq ((.call ((some ([73], (live19, .ln), .skip, 39, 7))) ((some 45)) [] none)) ((.seq .skip .skip)))))))) =>
      decide (live17 = Flapjack.sptListInsert [0] .ln) &&
      decide (live18 = Flapjack.sptListInsert [0] .ln) &&
      decide (live19 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment12 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 59 ((.const 0)))) ((.set ((.temp 8)) ((.var 59)))))) ((.seq ((.seq ((.assign 60 ((.lookup ((.temp 8)))))) ((.set ((.temp 9)) ((.var 60)))))) ((.seq ((.seq ((.assign 61 ((.lookup ((.temp 8)))))) ((.set ((.temp 10)) ((.var 61)))))) ((.seq ((.seq ((.assign 62 ((.shift .lsr ((.lookup ((.temp 1)))) (.const 1))))) ((.set ((.temp 1)) ((.var 62)))))) ((.seq ((.seq ((.assign 63 ((.shift .lsr ((.lookup ((.temp 2)))) (.const 1))))) ((.set ((.temp 2)) ((.var 63)))))) ((.seq fragment11 ((.seq ((.seq ((.assign 75 ((.lookup ((.temp 0)))))) ((.ite .equal 75 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 74 ((.lookup ((.temp 31)))))) ((.seq ((.set ((.temp 31)) ((.lookup ((.temp 30)))))) ((.set ((.temp 30)) ((.var 74)))))))) ((.seq .skip .skip)))))))) ((.seq ((.seq ((.assign 76 ((.shift .lsl ((.lookup ((.temp 10)))) (.const 1))))) ((.set ((.temp 10)) ((.var 76)))))) ((.seq ((.seq ((.assign 77 ((.op .add [(.lookup ((.temp 10))), (.lookup ((.temp 12)))])))) ((.set ((.temp 10)) ((.var 77)))))) ((.seq .skip .skip)))))))))))))))))))) =>
      matches_fragment11 fragment11
  | _ => false

private def matches_fragment13 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 49 ((.lookup ((.temp 10)))))) ((.seq ((.assign 50 ((.lookup ((.temp 11)))))) ((.ite .lower 49 ((.reg 50)) ((.seq ((.seq ((.assign 44 ((.const 1)))) ((.set ((.temp 10)) ((.var 44)))))) ((.seq .skip .skip)))) ((.seq ((.assign 47 ((.lookup ((.temp 11)))))) ((.seq ((.assign 48 ((.lookup ((.temp 10)))))) ((.ite .lower 47 ((.reg 48)) ((.seq ((.seq ((.assign 45 (.const 2))) ((.set ((.temp 10)) ((.var 45)))))) ((.seq .skip .skip)))) ((.seq ((.call ((some ([46], (live16, .ln), .skip, 39, 4))) ((some 42)) [] none)) ((.seq .skip .skip)))))))))))))))) ((.seq ((.assign 78 ((.lookup ((.temp 10)))))) ((.ite .equal 78 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.seq ((.assign 51 ((.const 0)))) ((.set ((.temp 0)) ((.var 51)))))) ((.seq ((.assign 58 ((.lookup ((.temp 10)))))) ((.ite .equal 58 ((.imm 1)) ((.seq ((.seq ((.assign 52 ((.lookup ((.temp 31)))))) ((.seq ((.set ((.temp 31)) ((.lookup ((.temp 30)))))) ((.set ((.temp 30)) ((.var 52)))))))) ((.seq ((.seq ((.assign 53 ((.op .xor [(.lookup ((.temp 12))), (.const 1)])))) ((.set ((.temp 12)) ((.var 53)))))) ((.seq ((.seq ((.assign 54 ((.const 1)))) ((.set ((.temp 0)) ((.var 54)))))) ((.seq .skip .skip)))))))) ((.seq ((.seq ((.assign 55 ((.lookup ((.temp 1)))))) ((.set ((.temp 8)) ((.var 55)))))) ((.seq ((.seq ((.assign 56 ((.lookup ((.temp 2)))))) ((.set ((.temp 1)) ((.var 56)))))) ((.seq ((.seq ((.assign 57 ((.lookup ((.temp 8)))))) ((.set ((.temp 2)) ((.var 57)))))) ((.seq .skip .skip)))))))))))))) fragment12)))))))) =>
      decide (live16 = Flapjack.sptListInsert [0] .ln) &&
      matches_fragment12 fragment12
  | _ => false

private def matches_fragment14 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 79 ((.reg 80)) ((.seq ((.seq ((.assign 9 ((.shift .lsr ((.lookup ((.temp 1)))) (.const 1))))) ((.set ((.temp 1)) ((.var 9)))))) ((.seq ((.seq ((.assign 10 ((.shift .lsr ((.lookup ((.temp 2)))) (.const 1))))) ((.set ((.temp 2)) ((.var 10)))))) ((.seq ((.seq ((.seq ((.assign 11 ((.const 0)))) ((.set ((.temp 0)) ((.var 11)))))) ((.seq ((.assign 17 ((.lookup ((.temp 1)))))) ((.seq ((.assign 18 ((.lookup ((.temp 2)))))) ((.ite .lower 17 ((.reg 18)) ((.seq ((.seq ((.assign 12 ((.lookup ((.temp 31)))))) ((.seq ((.set ((.temp 31)) ((.lookup ((.temp 30)))))) ((.set ((.temp 30)) ((.var 12)))))))) ((.seq ((.seq ((.assign 13 ((.const 1)))) ((.set ((.temp 0)) ((.var 13)))))) ((.seq .skip .skip)))))) ((.seq ((.seq ((.assign 14 ((.lookup ((.temp 1)))))) ((.set ((.temp 8)) ((.var 14)))))) ((.seq ((.seq ((.assign 15 ((.lookup ((.temp 2)))))) ((.set ((.temp 1)) ((.var 15)))))) ((.seq ((.seq ((.assign 16 ((.lookup ((.temp 8)))))) ((.set ((.temp 2)) ((.var 16)))))) ((.seq .skip .skip)))))))))))))))) ((.seq ((.seq ((.assign 19 ((.const 0)))) ((.set ((.temp 8)) ((.var 19)))))) fragment10)))))))) ((.seq ((.seq ((.assign 39 ((.lookup ((.temp 10)))))) ((.set ((.temp 12)) ((.var 39)))))) ((.seq ((.seq ((.assign 40 ((.lookup ((.temp 1)))))) ((.set ((.temp 10)) ((.var 40)))))) ((.seq ((.seq ((.assign 41 ((.shift .lsr ((.lookup ((.temp 10)))) (.const 1))))) ((.set ((.temp 10)) ((.var 41)))))) ((.seq ((.seq ((.assign 42 ((.lookup ((.temp 2)))))) ((.set ((.temp 11)) ((.var 42)))))) ((.seq ((.seq ((.assign 43 ((.shift .lsr ((.lookup ((.temp 11)))) (.const 1))))) ((.set ((.temp 11)) ((.var 43)))))) fragment13)))))))))))) =>
      matches_fragment10 fragment10 &&
      matches_fragment13 fragment13
  | _ => false

private def matches_fragment15 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 97 ((.shift .lsr ((.lookup ((.temp 7)))) (.const 1))))) ((.set ((.temp 7)) ((.var 97)))))) ((.seq ((.seq ((.assign 98 ((.lookup ((.temp 2)))))) ((.set ((.temp 9)) ((.var 98)))))) ((.seq ((.seq ((.assign 99 ((.shift .lsr ((.lookup ((.temp 9)))) (.const 1))))) ((.set ((.temp 9)) ((.var 99)))))) ((.seq ((.seq ((.assign 100 ((.const 0)))) ((.set ((.temp 10)) ((.var 100)))))) ((.seq ((.seq ((.assign 101 ((.const 0)))) ((.set ((.temp 12)) ((.var 101)))))) ((.seq ((.call ((some ([102], (live21, .ln), .skip, 39, 9))) ((some 47)) [] none)) ((.seq ((.seq ((.assign 103 ((.const 0)))) ((.set ((.temp 8)) ((.var 103)))))) ((.seq ((.call ((some ([104], (live22, .ln), .skip, 39, 10))) ((some 45)) [] none)) ((.seq ((.seq ((.assign 105 ((.shift .lsl ((.lookup ((.temp 10)))) (.const 1))))) ((.set ((.temp 10)) ((.var 105)))))) ((.seq ((.seq ((.assign 106 ((.op .add [(.lookup ((.temp 10))), (.lookup ((.temp 13)))])))) ((.set ((.temp 10)) ((.var 106)))))) ((.seq .skip .skip)))))))))))))))))))))) =>
      decide (live21 = Flapjack.sptListInsert [0] .ln) &&
      decide (live22 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment16 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 86 ((.shift .lsr ((.lookup ((.temp 10)))) (.const 1))))) ((.set ((.temp 10)) ((.var 86)))))) ((.seq ((.call ((some ([87], (live20, .ln), .skip, 39, 8))) ((some 46)) [] none)) ((.seq ((.seq ((.assign 88 ((.lookup ((.temp 1)))))) ((.set ((.temp 10)) ((.var 88)))))) ((.seq ((.seq ((.assign 89 ((.op .and [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 89)))))) ((.seq ((.seq ((.assign 90 ((.lookup ((.temp 2)))))) ((.set ((.temp 11)) ((.var 90)))))) ((.seq ((.seq ((.assign 91 ((.op .and [(.lookup ((.temp 11))), (.const 1)])))) ((.set ((.temp 11)) ((.var 91)))))) ((.seq ((.seq ((.assign 94 ((.lookup ((.temp 10)))))) ((.seq ((.assign 95 ((.lookup ((.temp 11)))))) ((.ite .equal 94 ((.reg 95)) ((.seq ((.seq ((.assign 92 ((.const 0)))) ((.set ((.temp 13)) ((.var 92)))))) .skip)) ((.seq ((.seq ((.assign 93 ((.const 1)))) ((.set ((.temp 13)) ((.var 93)))))) .skip)))))))) ((.seq ((.seq ((.assign 96 ((.lookup ((.temp 1)))))) ((.set ((.temp 7)) ((.var 96)))))) fragment15)))))))))))))))) =>
      decide (live20 = Flapjack.sptListInsert [0] .ln) &&
      matches_fragment15 fragment15
  | _ => false

private def matches_fragment17 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 137 ((.lookup ((.temp 8)))))) ((.set ((.temp 0)) ((.var 137)))))) ((.seq ((.seq ((.assign 138 ((.lookup ((.temp 14)))))) ((.set ((.temp 3)) ((.var 138)))))) ((.seq ((.assign 147 ((.lookup ((.temp 3)))))) ((.ite .equal 147 ((.imm 0)) ((.seq ((.assign 140 ((.lookup ((.temp 2)))))) ((.ite .equal 140 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 139 ((.const 1)))) ((.set ((.temp 6)) ((.var 139)))))) ((.seq .skip .skip)))))))) ((.seq ((.seq ((.assign 141 ((.const 1)))) ((.set ((.temp 0)) ((.var 141)))))) ((.seq ((.seq ((.assign 142 ((.const 0)))) ((.set ((.temp 10)) ((.var 142)))))) ((.seq ((.seq ((.assign 143 ((.lookup ((.temp 2)))))) ((.seq ((.assign 144 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 144)) 143)))))) ((.seq ((.assign 146 ((.lookup ((.temp 2)))))) ((.ite .equal 146 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 145 ((.const 1)))) ((.set ((.temp 6)) ((.var 145)))))) ((.seq .skip .skip)))))))))))))))))))))) =>
      true
  | _ => false

private def matches_fragment18 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 189 ((.lookup ((.temp 8)))))) ((.set ((.temp 7)) ((.var 189)))))) ((.seq ((.call ((some ([190], (live31, .ln), .skip, 39, 19))) ((some 45)) [] none)) ((.seq ((.seq ((.assign 191 ((.lookup ((.temp 10)))))) ((.set ((.temp 6)) ((.var 191)))))) ((.seq ((.seq ((.assign 192 ((.lookup ((.temp 9)))))) ((.set ((.temp 10)) ((.var 192)))))) ((.seq ((.seq ((.assign 193 ((.lookup ((.temp 18)))))) ((.set ((.temp 3)) ((.var 193)))))) ((.seq ((.seq ((.assign 194 ((.lookup ((.temp 7)))))) ((.set ((.temp 8)) ((.var 194)))))) ((.seq ((.assign 199 ((.lookup ((.temp 3)))))) ((.ite .equal 199 ((.imm 0)) ((.seq ((.seq ((.assign 195 ((.const 0)))) ((.set ((.temp 11)) ((.var 195)))))) ((.seq ((.call ((some ([196], (live32, .ln), .skip, 39, 20))) ((some 59)) [] none)) ((.seq ((.seq ((.assign 197 ((.lookup ((.temp 7)))))) ((.set ((.temp 0)) ((.var 197)))))) ((.seq .skip .skip)))))))) ((.seq ((.seq ((.assign 198 ((.lookup ((.temp 9)))))) ((.set ((.temp 0)) ((.var 198)))))) ((.seq .skip .skip)))))))))))))))))))) =>
      decide (live31 = Flapjack.sptListInsert [0] .ln) &&
      decide (live32 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment19 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 178 ((.lookup ((.temp 1)))))) ((.set ((.temp 15)) ((.var 178)))))) ((.seq ((.seq ((.assign 179 ((.lookup ((.temp 10)))))) ((.set ((.temp 17)) ((.var 179)))))) ((.seq ((.call ((some ([180], (live29, .ln), .skip, 39, 17))) ((some 54)) [] none)) ((.seq ((.seq ((.assign 181 ((.lookup ((.temp 17)))))) ((.set ((.temp 8)) ((.var 181)))))) ((.seq ((.seq ((.assign 182 ((.lookup ((.temp 9)))))) ((.set ((.temp 11)) ((.var 182)))))) ((.seq ((.seq ((.assign 183 ((.lookup ((.temp 9)))))) ((.set ((.temp 10)) ((.var 183)))))) ((.seq ((.seq ((.seq ((.assign 184 ((.lookup ((.temp 7)))))) ((.set ((.temp 9)) ((.var 184)))))) ((.seq ((.seq ((.assign 185 ((.const 0)))) ((.set ((.temp 2)) ((.var 185)))))) ((.seq ((.call ((some ([186], (live30, .ln), .skip, 39, 18))) ((some 58)) [] none)) ((.seq ((.seq ((.assign 187 ((.lookup ((.temp 11)))))) ((.set ((.temp 9)) ((.var 187)))))) ((.seq ((.seq ((.assign 188 ((.lookup ((.temp 9)))))) ((.set ((.temp 10)) ((.var 188)))))) fragment18)))))))))) ((.seq .skip .skip)))))))))))))))) =>
      decide (live29 = Flapjack.sptListInsert [0] .ln) &&
      decide (live30 = Flapjack.sptListInsert [0] .ln) &&
      matches_fragment18 fragment18
  | _ => false

private def matches_fragment20 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 167 ((.lookup ((.temp 0)))))) ((.set ((.temp 1)) ((.var 167)))))) ((.seq ((.seq ((.assign 168 ((.lookup ((.temp 0)))))) ((.set ((.temp 3)) ((.var 168)))))) ((.seq ((.seq ((.assign 169 ((.lookup ((.temp 0)))))) ((.set ((.temp 11)) ((.var 169)))))) ((.seq ((.seq ((.assign 170 ((.lookup ((.temp 7)))))) ((.set ((.temp 9)) ((.var 170)))))) ((.seq ((.call ((some ([171], (live28, .ln), .skip, 39, 16))) ((some 53)) [] none)) ((.seq ((.seq ((.assign 172 ((.lookup ((.temp 8)))))) ((.set ((.temp 7)) ((.var 172)))))) ((.seq ((.seq ((.assign 173 ((.lookup ((.temp 9)))))) ((.set ((.temp 11)) ((.var 173)))))) ((.seq ((.seq ((.assign 174 ((.lookup ((.temp 19)))))) ((.set ((.temp 10)) ((.var 174)))))) ((.seq ((.seq ((.assign 175 ((.op .sub [(.lookup ((.temp 10))), (.lookup ((.temp 9)))])))) ((.set ((.temp 10)) ((.var 175)))))) ((.seq ((.seq ((.assign 176 ((.op .add [(.lookup ((.temp 10))), (.const 2)])))) ((.set ((.temp 10)) ((.var 176)))))) ((.seq ((.seq ((.assign 177 ((.lookup ((.temp 0)))))) ((.set ((.temp 14)) ((.var 177)))))) fragment19)))))))))))))))))))))) =>
      decide (live28 = Flapjack.sptListInsert [0] .ln) &&
      matches_fragment19 fragment19
  | _ => false

private def matches_fragment21 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 156 ((.const 1)))) ((.set ((.temp 2)) ((.var 156)))))) ((.seq ((.call ((some ([157], (live26, .ln), .skip, 39, 14))) ((some 51)) [] none)) ((.seq ((.seq ((.seq ((.assign 158 ((.const 0)))) ((.set ((.temp 1)) ((.var 158)))))) ((.seq ((.seq ((.assign 159 ((.lookup ((.temp 2)))))) ((.set ((.temp 8)) ((.var 159)))))) ((.seq ((.seq ((.assign 160 ((.lookup ((.temp 1)))))) ((.set ((.temp 10)) ((.var 160)))))) ((.seq ((.seq ((.assign 161 ((.lookup ((.temp 1)))))) ((.set ((.temp 11)) ((.var 161)))))) ((.seq ((.call ((some ([162], (live27, .ln), .skip, 39, 15))) ((some 52)) [] none)) ((.seq ((.seq ((.assign 163 ((.const 0)))) ((.set ((.temp 1)) ((.var 163)))))) ((.seq ((.seq ((.assign 164 ((.lookup ((.temp 1)))))) ((.seq ((.assign 165 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 165)) 164)))))) ((.seq ((.seq ((.assign 166 ((.const 0)))) ((.set ((.temp 0)) ((.var 166)))))) fragment20)))))))))))))))) ((.seq .skip .skip)))))))) =>
      decide (live26 = Flapjack.sptListInsert [0] .ln) &&
      decide (live27 = Flapjack.sptListInsert [0] .ln) &&
      matches_fragment20 fragment20
  | _ => false

private def matches_fragment22 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 200 ((.imm 1)) ((.seq ((.seq ((.seq ((.assign 128 ((.lookup ((.temp 3)))))) ((.set ((.temp 14)) ((.var 128)))))) ((.seq ((.seq ((.assign 129 ((.const 0)))) ((.set ((.temp 2)) ((.var 129)))))) ((.seq ((.seq ((.assign 130 ((.lookup ((.temp 2)))))) ((.set ((.temp 10)) ((.var 130)))))) ((.seq ((.seq ((.assign 131 ((.op .add [(.lookup ((.temp 30))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 132 ((.load ((.var 131)))))) ((.set ((.temp 9)) ((.var 132)))))))) ((.seq ((.seq ((.assign 133 ((.lookup ((.temp 0)))))) ((.set ((.temp 10)) ((.var 133)))))) ((.seq ((.seq ((.assign 134 ((.lookup ((.temp 0)))))) ((.set ((.temp 8)) ((.var 134)))))) ((.seq ((.call ((some ([135], (live25, .ln), .skip, 39, 13))) ((some 50)) [] none)) ((.seq ((.seq ((.assign 136 ((.const 0)))) ((.set ((.temp 6)) ((.var 136)))))) fragment17)))))))))))))))) ((.seq .skip .skip)))) ((.seq ((.seq ((.assign 148 ((.lookup ((.temp 3)))))) ((.set ((.temp 18)) ((.var 148)))))) ((.seq ((.seq ((.assign 149 ((.lookup ((.temp 0)))))) ((.set ((.temp 19)) ((.var 149)))))) ((.seq ((.seq ((.assign 150 ((.lookup ((.temp 1)))))) ((.set ((.temp 7)) ((.var 150)))))) ((.seq ((.seq ((.assign 151 ((.lookup ((.temp 0)))))) ((.set ((.temp 9)) ((.var 151)))))) ((.seq ((.seq ((.assign 152 ((.lookup ((.temp 1)))))) ((.set ((.temp 10)) ((.var 152)))))) ((.seq ((.seq ((.assign 153 ((.op .sub [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 153)))))) ((.seq ((.seq ((.assign 154 ((.op .add [(.lookup ((.temp 30))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 155 ((.load ((.var 154)))))) ((.set ((.temp 1)) ((.var 155)))))))) fragment21)))))))))))))))) =>
      decide (live25 = Flapjack.sptListInsert [0] .ln) &&
      matches_fragment17 fragment17 &&
      matches_fragment21 fragment21
  | _ => false

private def matches_fragment23 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .lower 201 ((.reg 202)) ((.seq ((.seq ((.seq ((.assign 118 ((.lookup ((.temp 0)))))) ((.set ((.temp 6)) ((.var 118)))))) ((.seq ((.assign 127 ((.lookup ((.temp 3)))))) ((.ite .equal 127 ((.imm 0)) ((.seq ((.seq ((.assign 119 ((.const 0)))) ((.set ((.temp 0)) ((.var 119)))))) ((.seq .skip .skip)))) ((.seq ((.seq ((.assign 120 ((.lookup ((.temp 0)))))) ((.set ((.temp 11)) ((.var 120)))))) ((.seq ((.seq ((.assign 121 ((.lookup ((.temp 1)))))) ((.set ((.temp 10)) ((.var 121)))))) ((.seq ((.seq ((.assign 122 ((.const 0)))) ((.set ((.temp 0)) ((.var 122)))))) ((.seq ((.call ((some ([123], (live23, .ln), .skip, 39, 11))) ((some 46)) [] none)) ((.seq ((.seq ((.assign 124 ((.lookup ((.temp 11)))))) ((.set ((.temp 10)) ((.var 124)))))) ((.seq ((.call ((some ([125], (live24, .ln), .skip, 39, 12))) ((some 49)) [] none)) ((.seq ((.seq ((.assign 126 ((.lookup ((.temp 1)))))) ((.set ((.temp 0)) ((.var 126)))))) ((.seq .skip .skip)))))))))))))))))))))) ((.seq .skip .skip)))) ((.seq ((.assign 200 ((.lookup ((.temp 1)))))) fragment22)))) =>
      decide (live23 = Flapjack.sptListInsert [0] .ln) &&
      decide (live24 = Flapjack.sptListInsert [0] .ln) &&
      matches_fragment22 fragment22
  | _ => false

private def matches_fragment24 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 215 ((.lookup ((.temp 2)))))) ((.ite .equal 215 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.assign 214 ((.lookup ((.temp 6)))))) ((.ite .equal 214 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 210 ((.const 0)))) ((.set ((.temp 2)) ((.var 210)))))) ((.seq ((.seq ((.assign 211 ((.lookup ((.temp 2)))))) ((.set ((.temp 10)) ((.var 211)))))) ((.seq ((.seq ((.assign 212 ((.op .xor [(.lookup ((.temp 2))), (.op .sub [(.const 0), (.const 1)])])))) ((.set ((.temp 2)) ((.var 212)))))) ((.seq ((.call ((some ([213], (live34, .ln), .skip, 39, 22))) ((some 60)) [] none)) ((.seq .skip .skip)))))))))))))))))) ((.seq ((.assign 218 ((.lookup ((.temp 11)))))) ((.ite .equal 218 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 216 ((.shift .lsl ((.lookup ((.temp 11)))) (.const 1))))) ((.set ((.temp 11)) ((.var 216)))))) ((.seq ((.seq ((.assign 217 ((.op .add [(.lookup ((.temp 11))), (.lookup ((.temp 3)))])))) ((.set ((.temp 11)) ((.var 217)))))) ((.seq .skip .skip)))))))))))) =>
      decide (live34 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment25 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 232 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 222 ((.lookup ((.temp 6)))))) ((.set ((.temp 8)) ((.var 222)))))) ((.seq ((.seq ((.assign 223 ((.lookup ((.temp 6)))))) ((.set ((.temp 9)) ((.var 223)))))) ((.seq ((.seq ((.assign 224 ((.lookup ((.temp 1)))))) ((.set ((.temp 3)) ((.var 224)))))) ((.seq ((.seq ((.seq ((.seq ((.assign 225 ((.const 0)))) ((.set ((.temp 10)) ((.var 225)))))) ((.seq ((.seq ((.assign 226 ((.op .add [(.lookup ((.temp 1))), (.const 1)])))) ((.set ((.temp 1)) ((.var 226)))))) ((.seq ((.seq ((.assign 227 ((.const 1)))) ((.set ((.temp 4)) ((.var 227)))))) ((.seq ((.call ((some ([228], (live35, .ln), .skip, 39, 23))) ((some 61)) [] none)) .skip)))))))) ((.seq .skip .skip)))) ((.seq ((.seq ((.assign 229 ((.lookup ((.temp 3)))))) ((.set ((.temp 10)) ((.var 229)))))) ((.seq ((.call ((some ([230], (live36, .ln), .skip, 39, 24))) ((some 45)) [] none)) ((.seq ((.seq ((.assign 231 ((.lookup ((.temp 10)))))) ((.set ((.temp 6)) ((.var 231)))))) ((.seq .skip .skip)))))))))))))))))) =>
      decide (live35 = Flapjack.sptListInsert [0] .ln) &&
      decide (live36 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment26 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 239 ((.imm 0)) ((.seq ((.seq ((.assign 204 ((.lookup ((.temp 0)))))) ((.set ((.temp 10)) ((.var 204)))))) ((.seq ((.seq ((.assign 205 ((.lookup ((.temp 10)))))) ((.set ((.temp 8)) ((.var 205)))))) ((.seq ((.call ((some ([206], (live33, .ln), .skip, 39, 21))) ((some 45)) [] none)) ((.seq ((.seq ((.assign 207 ((.lookup ((.temp 10)))))) ((.set ((.temp 11)) ((.var 207)))))) ((.seq ((.seq ((.assign 208 ((.lookup ((.temp 20)))))) ((.set ((.temp 2)) ((.var 208)))))) ((.seq ((.seq ((.assign 209 ((.lookup ((.temp 2)))))) ((.set ((.temp 3)) ((.var 209)))))) fragment24)))))))))))) ((.seq ((.seq ((.assign 219 ((.lookup ((.temp 20)))))) ((.set ((.temp 2)) ((.var 219)))))) ((.seq ((.seq ((.assign 220 ((.lookup ((.temp 11)))))) ((.set ((.temp 1)) ((.var 220)))))) ((.seq ((.seq ((.assign 221 ((.shift .lsr ((.lookup ((.temp 1)))) (.const 1))))) ((.set ((.temp 1)) ((.var 221)))))) ((.seq ((.seq ((.assign 233 ((.lookup ((.temp 2)))))) ((.ite .equal 233 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.assign 232 ((.lookup ((.temp 6)))))) fragment25)))))) ((.seq ((.seq ((.assign 237 ((.lookup ((.temp 6)))))) ((.ite .equal 237 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 234 ((.shift .lsl ((.lookup ((.temp 6)))) (.const 1))))) ((.set ((.temp 6)) ((.var 234)))))) ((.seq ((.assign 236 ((.lookup ((.temp 11)))))) ((.ite .test 236 ((.imm 1)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 235 ((.op .add [(.lookup ((.temp 6))), (.const 1)])))) ((.set ((.temp 6)) ((.var 235)))))) ((.seq .skip .skip)))))))))))))) ((.seq ((.seq ((.assign 238 ((.lookup ((.temp 6)))))) ((.set ((.temp 11)) ((.var 238)))))) ((.seq .skip .skip)))))))))))))))) =>
      decide (live33 = Flapjack.sptListInsert [0] .ln) &&
      matches_fragment24 fragment24 &&
      matches_fragment25 fragment25
  | _ => false

private def matches_fragment27 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.seq ((.assign 112 ((.shift .lsr ((.lookup ((.temp 10)))) (.const 1))))) ((.set ((.temp 0)) ((.var 112)))))) ((.seq ((.seq ((.assign 113 ((.shift .lsr ((.lookup ((.temp 11)))) (.const 1))))) ((.set ((.temp 1)) ((.var 113)))))) ((.seq ((.seq ((.assign 114 ((.op .xor [(.lookup ((.temp 10))), (.lookup ((.temp 11)))])))) ((.set ((.temp 10)) ((.var 114)))))) ((.seq ((.seq ((.assign 115 ((.op .and [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 115)))))) ((.seq ((.seq ((.assign 116 ((.lookup ((.temp 10)))))) ((.set ((.temp 20)) ((.var 116)))))) ((.seq ((.seq ((.assign 117 ((.lookup ((.temp 11)))))) ((.set ((.temp 21)) ((.var 117)))))) ((.seq ((.seq ((.assign 201 ((.lookup ((.temp 0)))))) ((.seq ((.assign 202 ((.lookup ((.temp 1)))))) fragment23)))) ((.seq ((.seq ((.assign 203 ((.lookup ((.temp 21)))))) ((.set ((.temp 11)) ((.var 203)))))) ((.seq ((.seq ((.assign 239 ((.lookup ((.temp 3)))))) fragment26)) ((.seq .skip .skip)))))))))))))))))))) ((.seq ((.seq ((.assign 240 ((.lookup ((.temp 11)))))) ((.set ((.temp 10)) ((.var 240)))))) ((.seq .skip .skip)))))) =>
      matches_fragment23 fragment23 &&
      matches_fragment26 fragment26
  | _ => false

private def matches_fragment28 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 241 ((.imm 4)) ((.seq ((.seq ((.assign 81 ((.lookup ((.temp 1)))))) ((.set ((.temp 2)) ((.var 81)))))) ((.seq ((.seq ((.assign 82 ((.lookup ((.temp 0)))))) ((.set ((.temp 1)) ((.var 82)))))) ((.seq ((.seq ((.seq ((.assign 83 ((.const 0)))) ((.set ((.temp 10)) ((.var 83)))))) ((.seq ((.assign 108 ((.lookup ((.temp 1)))))) ((.ite .equal 108 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.assign 107 ((.lookup ((.temp 2)))))) ((.ite .equal 107 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 84 ((.const 0)))) ((.set ((.temp 0)) ((.var 84)))))) ((.seq ((.seq ((.assign 85 ((.lookup ((.temp 2)))))) ((.set ((.temp 10)) ((.var 85)))))) fragment16)))))))))))))) ((.seq .skip .skip)))))))) ((.seq ((.seq ((.assign 109 ((.op .sub [(.lookup ((.temp 3))), (.const 5)])))) ((.set ((.temp 3)) ((.var 109)))))) ((.seq ((.seq ((.assign 110 ((.lookup ((.temp 0)))))) ((.set ((.temp 10)) ((.var 110)))))) ((.seq ((.seq ((.assign 111 ((.lookup ((.temp 1)))))) ((.set ((.temp 11)) ((.var 111)))))) fragment27)))))))) =>
      matches_fragment16 fragment16 &&
      matches_fragment27 fragment27
  | _ => false

private def matches_fragment29 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .lower 242 ((.imm 2)) ((.seq ((.seq ((.assign 2 ((.lookup ((.temp 3)))))) ((.ite .equal 2 ((.imm 0)) .skip ((.seq ((.seq ((.assign 1 ((.op .xor [(.lookup ((.temp 1))), (.const 1)])))) ((.set ((.temp 1)) ((.var 1)))))) .skip)))))) ((.seq ((.seq ((.assign 3 ((.lookup ((.temp 1)))))) ((.set ((.temp 2)) ((.var 3)))))) ((.seq ((.seq ((.assign 4 ((.lookup ((.temp 0)))))) ((.set ((.temp 1)) ((.var 4)))))) ((.seq ((.seq ((.seq ((.assign 5 ((.lookup ((.temp 1)))))) ((.set ((.temp 10)) ((.var 5)))))) ((.seq ((.seq ((.assign 6 ((.op .and [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 6)))))) ((.seq ((.seq ((.assign 7 ((.lookup ((.temp 2)))))) ((.set ((.temp 11)) ((.var 7)))))) ((.seq ((.seq ((.assign 8 ((.op .and [(.lookup ((.temp 11))), (.const 1)])))) ((.set ((.temp 11)) ((.var 8)))))) ((.seq ((.assign 79 ((.lookup ((.temp 10)))))) ((.seq ((.assign 80 ((.lookup ((.temp 11)))))) fragment14)))))))))))) ((.seq .skip .skip)))))))))) ((.seq ((.assign 241 ((.lookup ((.temp 3)))))) fragment28)))) =>
      matches_fragment14 fragment14 &&
      matches_fragment28 fragment28
  | _ => false

private def matches_fragment30 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 3 ((.op .add [(.lookup ((.temp 30))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 4 ((.load ((.var 3)))))) ((.set ((.temp 8)) ((.var 4)))))))) ((.seq ((.seq ((.assign 5 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 6 ((.load ((.var 5)))))) ((.set ((.temp 9)) ((.var 6)))))))) ((.seq ((.seq ((.assign 11 ((.lookup ((.temp 4)))))) ((.seq ((.assign 10 ((.lookup ((.temp 9)))))) ((.seq ((.assign 10 ((.op .xor [(.var 10), (.const 18446744073709551615)])))) ((.seq ((.assign 9 ((.lookup ((.temp 8)))))) ((.seq ((.inst ((.arith ((.addCarry 8 9 10 11)))))) ((.seq ((.set ((.temp 8)) ((.var 8)))) ((.set ((.temp 4)) ((.var 11)))))))))))))))) ((.seq ((.seq ((.assign 12 ((.lookup ((.temp 8)))))) ((.seq ((.assign 13 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 13)) 12)))))) ((.seq ((.seq ((.assign 14 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 14)))))) ((.call none ((some 61)) [0] none)))))))))))) =>
      true
  | _ => false

private def matches_fragment31 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 16 ((.reg 17)) ((.seq ((.seq ((.assign 1 ((.const 1)))) ((.set ((.temp 0)) ((.var 1)))))) ((.seq ((.seq ((.assign 2 ((.lookup ((.temp 0)))))) ((.seq ((.assign 3 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 3)) 2)))))) ((.seq ((.seq ((.assign 4 ((.op .add [(.lookup ((.temp 11))), (.const 1)])))) ((.set ((.temp 11)) ((.var 4)))))) ((.seq .skip .skip)))))))) ((.seq ((.seq ((.assign 5 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 6 ((.load ((.var 5)))))) ((.set ((.temp 0)) ((.var 6)))))))) ((.seq ((.assign 14 ((.lookup ((.temp 0)))))) ((.seq ((.assign 15 ((.lookup ((.temp 2)))))) ((.ite .equal 14 ((.reg 15)) ((.seq ((.seq ((.assign 7 ((.const 0)))) ((.set ((.temp 0)) ((.var 7)))))) ((.seq ((.seq ((.assign 8 ((.lookup ((.temp 0)))))) ((.seq ((.assign 9 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 9)) 8)))))) ((.seq ((.seq ((.assign 10 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 10)))))) ((.seq .skip ((.call none ((some 60)) [0] none)))))))))) ((.seq ((.seq ((.assign 11 ((.op .add [(.lookup ((.temp 0))), (.const 1)])))) ((.set ((.temp 0)) ((.var 11)))))) ((.seq ((.seq ((.assign 12 ((.lookup ((.temp 0)))))) ((.seq ((.assign 13 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 13)) 12)))))) ((.seq .skip .skip)))))))))))))))) =>
      true
  | _ => false

private def matches_fragment32 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 11 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 1)))))) ((.seq ((.seq ((.assign 2 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 3 ((.load ((.var 2)))))) ((.set ((.temp 0)) ((.var 3)))))))) ((.seq ((.seq ((.seq ((.assign 8 ((.lookup ((.temp 9)))))) ((.seq ((.assign 7 ((.lookup ((.temp 0)))))) ((.seq ((.assign 6 ((.lookup ((.temp 2)))))) ((.seq ((.mustTerminate ((.seq ((.call ((some ([4], (live37, .ln), .skip, 58, 2))) ((some 23)) [6, 7, 8] none)) ((.assign 5 ((.lookup ((.temp 28)))))))))) ((.seq ((.set ((.temp 0)) ((.var 4)))) ((.set ((.temp 2)) ((.var 5)))))))))))))) .skip)) ((.seq ((.seq ((.assign 9 ((.lookup ((.temp 0)))))) ((.seq ((.assign 10 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 10)) 9)))))) ((.seq .skip ((.call none ((some 58)) [0] none)))))))))))))) =>
      decide (live37 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment33 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 23 ((.lookup ((.temp 11)))))) ((.set ((.temp 2)) ((.var 23)))))) ((.seq ((.seq ((.assign 31 ((.lookup ((.temp 2)))))) ((.seq ((.assign 32 ((.lookup ((.temp 1)))))) ((.ite .lower 31 ((.reg 32)) ((.seq ((.seq ((.assign 28 ((.lookup ((.temp 1)))))) ((.seq ((.assign 27 ((.lookup ((.temp 0)))))) ((.seq ((.assign 26 ((.lookup ((.temp 2)))))) ((.seq ((.mustTerminate ((.seq ((.call ((some ([24], (live38, .ln), .skip, 54, 2))) ((some 23)) [26, 27, 28] none)) ((.assign 25 ((.lookup ((.temp 28)))))))))) ((.seq ((.set ((.temp 0)) ((.var 24)))) ((.set ((.temp 2)) ((.var 25)))))))))))))) .skip)) ((.seq ((.seq ((.assign 29 ((.const 0)))) ((.set ((.temp 0)) ((.var 29)))))) ((.seq ((.seq ((.assign 30 ((.op .xor [(.lookup ((.temp 0))), (.op .sub [(.const 0), (.const 1)])])))) ((.set ((.temp 0)) ((.var 30)))))) .skip)))))))))) ((.seq ((.seq ((.assign 33 ((.lookup ((.temp 0)))))) ((.set ((.temp 6)) ((.var 33)))))) ((.seq ((.call ((some ([34], (live39, .ln), .skip, 54, 3))) ((some 55)) [] none)) ((.seq .skip .skip)))))))))) =>
      decide (live38 = Flapjack.sptListInsert [0] .ln) &&
      decide (live39 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment34 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 54 ((.lookup ((.temp 1)))))) ((.set ((.temp 8)) ((.var 54)))))) ((.seq ((.seq ((.assign 55 ((.const 1)))) ((.set ((.temp 8)) ((.var 55)))))) ((.seq ((.seq ((.assign 56 ((.lookup ((.temp 1)))))) ((.set ((.temp 11)) ((.var 56)))))) ((.seq ((.seq ((.assign 57 ((.lookup ((.temp 1)))))) ((.set ((.temp 12)) ((.var 57)))))) ((.seq ((.call ((some ([58], (live41, .ln), .skip, 54, 5))) ((some 57)) [] none)) ((.seq ((.seq ((.assign 59 ((.op .sub [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 59)))))) ((.seq ((.seq ((.assign 60 ((.lookup ((.temp 7)))))) ((.seq ((.assign 61 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 61)) 60)))))) ((.seq ((.seq ((.assign 62 ((.op .sub [(.lookup ((.temp 10))), (.lookup ((.temp 9)))])))) ((.set ((.temp 10)) ((.var 62)))))) ((.seq ((.seq ((.assign 63 ((.lookup ((.temp 6)))))) ((.set ((.temp 7)) ((.var 63)))))) ((.seq .skip ((.call none ((some 54)) [0] none)))))))))))))))))))))) =>
      decide (live41 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment35 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.seq ((.assign 43 ((.const 0)))) ((.set ((.temp 1)) ((.var 43)))))) ((.seq ((.seq ((.assign 44 ((.lookup ((.temp 1)))))) ((.set ((.temp 8)) ((.var 44)))))) ((.seq ((.seq ((.assign 45 ((.lookup ((.temp 1)))))) ((.set ((.temp 11)) ((.var 45)))))) ((.seq ((.seq ((.assign 46 ((.lookup ((.temp 1)))))) ((.set ((.temp 12)) ((.var 46)))))) ((.seq ((.call ((some ([47], (live40, .ln), .skip, 54, 4))) ((some 56)) [] none)) ((.seq ((.assign 50 ((.lookup ((.temp 7)))))) ((.ite .equal 50 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.assign 49 ((.lookup ((.temp 8)))))) ((.ite .equal 49 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 48 ((.op .sub [(.lookup ((.temp 7))), (.const 1)])))) ((.set ((.temp 7)) ((.var 48)))))) ((.seq .skip .skip)))))))))))))))))))))) ((.seq ((.seq ((.assign 51 ((.op .sub [(.lookup ((.temp 10))), (.lookup ((.temp 9)))])))) ((.set ((.temp 10)) ((.var 51)))))) ((.seq ((.seq ((.assign 52 ((.op .sub [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 52)))))) ((.seq ((.seq ((.assign 53 ((.const 0)))) ((.set ((.temp 1)) ((.var 53)))))) fragment34)))))))) =>
      decide (live40 = Flapjack.sptListInsert [0] .ln) &&
      matches_fragment34 fragment34
  | _ => false

private def matches_fragment36 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 20 ((.lookup ((.temp 6)))))) ((.set ((.temp 8)) ((.var 20)))))) ((.seq ((.seq ((.seq ((.assign 21 ((.lookup ((.temp 10)))))) ((.set ((.temp 0)) ((.var 21)))))) ((.seq ((.seq ((.assign 22 ((.lookup ((.temp 8)))))) ((.set ((.temp 1)) ((.var 22)))))) fragment33)))) ((.seq ((.seq ((.assign 35 ((.lookup ((.temp 6)))))) ((.set ((.temp 0)) ((.var 35)))))) ((.seq ((.seq ((.assign 36 ((.lookup ((.temp 14)))))) ((.set ((.temp 6)) ((.var 36)))))) ((.seq ((.seq ((.assign 37 ((.lookup ((.temp 15)))))) ((.set ((.temp 9)) ((.var 37)))))) ((.seq ((.seq ((.assign 38 ((.lookup ((.temp 16)))))) ((.set ((.temp 10)) ((.var 38)))))) ((.seq ((.seq ((.assign 39 ((.op .sub [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 39)))))) ((.seq ((.seq ((.assign 40 ((.lookup ((.temp 7)))))) ((.set ((.temp 15)) ((.var 40)))))) ((.seq ((.seq ((.assign 41 ((.lookup ((.temp 8)))))) ((.set ((.temp 14)) ((.var 41)))))) ((.seq ((.seq ((.assign 42 ((.lookup ((.temp 0)))))) ((.set ((.temp 7)) ((.var 42)))))) fragment35)))))))))))))))))))) =>
      matches_fragment33 fragment33 &&
      matches_fragment35 fragment35
  | _ => false

private def matches_fragment37 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 10 ((.op .sub [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 10)))))) ((.seq ((.seq ((.assign 11 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 12 ((.load ((.var 11)))))) ((.set ((.temp 1)) ((.var 12)))))))) ((.seq ((.seq ((.assign 13 ((.op .sub [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 13)))))) ((.seq ((.seq ((.assign 14 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 15 ((.load ((.var 14)))))) ((.set ((.temp 2)) ((.var 15)))))))) ((.seq ((.seq ((.assign 16 ((.lookup ((.temp 0)))))) ((.set ((.temp 11)) ((.var 16)))))) ((.seq ((.seq ((.assign 17 ((.lookup ((.temp 1)))))) ((.set ((.temp 10)) ((.var 17)))))) ((.seq ((.seq ((.assign 18 ((.lookup ((.temp 2)))))) ((.set ((.temp 9)) ((.var 18)))))) ((.seq ((.seq ((.assign 19 ((.lookup ((.temp 3)))))) ((.set ((.temp 7)) ((.var 19)))))) fragment36)))))))))))))))) =>
      matches_fragment36 fragment36
  | _ => false

private def matches_fragment38 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.seq ((.assign 56 ((.lookup ((.temp 8)))))) ((.seq ((.assign 55 ((.lookup ((.temp 0)))))) ((.seq ((.assign 55 ((.op .xor [(.var 55), (.const 18446744073709551615)])))) ((.seq ((.assign 54 ((.lookup ((.temp 3)))))) ((.seq ((.inst ((.arith ((.addCarry 53 54 55 56)))))) ((.seq ((.set ((.temp 3)) ((.var 53)))) ((.set ((.temp 8)) ((.var 56)))))))))))))))) .skip)) ((.seq ((.seq ((.assign 57 ((.lookup ((.temp 1)))))) ((.set ((.temp 0)) ((.var 57)))))) ((.seq ((.seq ((.assign 58 ((.lookup ((.temp 3)))))) ((.set ((.temp 1)) ((.var 58)))))) ((.seq ((.seq ((.assign 59 ((.lookup ((.temp 1)))))) ((.seq ((.assign 60 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 60)) 59)))))) ((.seq ((.seq ((.assign 61 ((.lookup ((.temp 0)))))) ((.set ((.temp 1)) ((.var 61)))))) ((.seq ((.seq ((.assign 62 ((.op .add [(.lookup ((.temp 11))), (.const 1)])))) ((.set ((.temp 11)) ((.var 62)))))) ((.seq ((.seq ((.assign 63 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 63)))))) ((.seq .skip ((.call none ((some 57)) [0] none)))))))))))))))))) =>
      true
  | _ => false

private def matches_fragment39 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.seq ((.assign 37 ((.lookup ((.temp 2)))))) ((.seq ((.assign 36 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.longMul 34 35 36 37)))))) ((.seq ((.set ((.temp 2)) ((.var 34)))) ((.set ((.temp 0)) ((.var 35)))))))))))) ((.seq ((.seq ((.assign 42 ((.const 0)))) ((.seq ((.assign 41 ((.lookup ((.temp 1)))))) ((.seq ((.assign 40 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.addCarry 39 40 41 42)))))) ((.seq ((.set ((.temp 0)) ((.var 39)))) ((.set ((.temp 4)) ((.var 42)))))))))))))) ((.seq ((.seq ((.assign 47 ((.lookup ((.temp 4)))))) ((.seq ((.assign 46 ((.const 0)))) ((.seq ((.assign 45 ((.lookup ((.temp 2)))))) ((.seq ((.inst ((.arith ((.addCarry 44 45 46 47)))))) ((.seq ((.set ((.temp 2)) ((.var 44)))) ((.set ((.temp 4)) ((.var 47)))))))))))))) ((.seq .skip .skip)))))))) ((.seq ((.seq ((.assign 48 ((.lookup ((.temp 12)))))) ((.set ((.temp 1)) ((.var 48)))))) ((.seq ((.seq ((.assign 49 ((.lookup ((.temp 2)))))) ((.set ((.temp 12)) ((.var 49)))))) ((.seq ((.seq ((.assign 50 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 51 ((.load ((.var 50)))))) ((.set ((.temp 3)) ((.var 51)))))))) fragment38)))))))) =>
      matches_fragment38 fragment38
  | _ => false

private def matches_fragment40 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.seq ((.assign 19 ((.lookup ((.temp 2)))))) ((.seq ((.assign 18 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.longMul 16 17 18 19)))))) ((.seq ((.set ((.temp 2)) ((.var 16)))) ((.set ((.temp 0)) ((.var 17)))))))))))) ((.seq ((.seq ((.assign 24 ((.const 0)))) ((.seq ((.assign 23 ((.lookup ((.temp 1)))))) ((.seq ((.assign 22 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.addCarry 21 22 23 24)))))) ((.seq ((.set ((.temp 0)) ((.var 21)))) ((.set ((.temp 4)) ((.var 24)))))))))))))) ((.seq ((.seq ((.assign 29 ((.lookup ((.temp 4)))))) ((.seq ((.assign 28 ((.const 0)))) ((.seq ((.assign 27 ((.lookup ((.temp 2)))))) ((.seq ((.inst ((.arith ((.addCarry 26 27 28 29)))))) ((.seq ((.set ((.temp 2)) ((.var 26)))) ((.set ((.temp 4)) ((.var 29)))))))))))))) ((.seq .skip .skip)))))))) ((.seq ((.seq ((.assign 30 ((.lookup ((.temp 12)))))) ((.set ((.temp 1)) ((.var 30)))))) ((.seq ((.seq ((.assign 31 ((.lookup ((.temp 2)))))) ((.set ((.temp 12)) ((.var 31)))))) ((.seq ((.seq ((.assign 32 ((.lookup ((.temp 0)))))) ((.set ((.temp 2)) ((.var 32)))))) ((.seq ((.seq ((.assign 33 ((.lookup ((.temp 7)))))) ((.set ((.temp 0)) ((.var 33)))))) fragment39)))))))))) =>
      matches_fragment39 fragment39
  | _ => false

private def matches_fragment41 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 64 ((.reg 65)) ((.seq ((.seq ((.assign 1 ((.lookup ((.temp 12)))))) ((.set ((.temp 0)) ((.var 1)))))) ((.seq ((.seq ((.assign 2 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 3 ((.load ((.var 2)))))) ((.set ((.temp 3)) ((.var 3)))))))) ((.seq ((.seq ((.seq ((.assign 8 ((.lookup ((.temp 8)))))) ((.seq ((.assign 7 ((.lookup ((.temp 0)))))) ((.seq ((.assign 7 ((.op .xor [(.var 7), (.const 18446744073709551615)])))) ((.seq ((.assign 6 ((.lookup ((.temp 3)))))) ((.seq ((.inst ((.arith ((.addCarry 5 6 7 8)))))) ((.seq ((.set ((.temp 3)) ((.var 5)))) ((.set ((.temp 8)) ((.var 8)))))))))))))))) .skip)) ((.seq ((.seq ((.assign 9 ((.lookup ((.temp 3)))))) ((.set ((.temp 1)) ((.var 9)))))) ((.seq ((.seq ((.assign 10 ((.lookup ((.temp 1)))))) ((.seq ((.assign 11 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 11)) 10)))))) ((.seq ((.seq ((.assign 12 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 12)))))) ((.seq .skip .skip)))))))))))))) ((.seq ((.seq ((.assign 13 ((.lookup ((.temp 6)))))) ((.set ((.temp 0)) ((.var 13)))))) ((.seq ((.seq ((.assign 14 ((.op .add [(.lookup ((.temp 30))), (.shift .lsl ((.lookup ((.temp 11)))) (.const 3))])))) ((.seq ((.assign 15 ((.load ((.var 14)))))) ((.set ((.temp 2)) ((.var 15)))))))) fragment40)))))) =>
      matches_fragment40 fragment40
  | _ => false

private def matches_fragment42 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 47 ((.lookup ((.temp 2)))))) ((.set ((.temp 12)) ((.var 47)))))) ((.seq ((.seq ((.assign 48 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 49 ((.load ((.var 48)))))) ((.set ((.temp 3)) ((.var 49)))))))) ((.seq ((.seq ((.assign 54 ((.lookup ((.temp 0)))))) ((.seq ((.assign 55 ((.lookup ((.temp 3)))))) ((.ite .equal 54 ((.reg 55)) .skip ((.seq ((.seq ((.assign 50 ((.const 1)))) ((.set ((.temp 8)) ((.var 50)))))) ((.seq ((.assign 52 ((.lookup ((.temp 3)))))) ((.seq ((.assign 53 ((.lookup ((.temp 0)))))) ((.ite .lower 52 ((.reg 53)) .skip ((.seq ((.seq ((.assign 51 ((.const 0)))) ((.set ((.temp 8)) ((.var 51)))))) .skip)))))))))))))))) ((.seq ((.seq ((.assign 56 ((.op .add [(.lookup ((.temp 11))), (.const 1)])))) ((.set ((.temp 11)) ((.var 56)))))) ((.seq ((.seq ((.assign 57 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 57)))))) ((.seq .skip ((.call none ((some 56)) [0] none)))))))))))))) =>
      true
  | _ => false

private def matches_fragment43 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 31 ((.lookup ((.temp 7)))))) ((.set ((.temp 0)) ((.var 31)))))) ((.seq ((.seq ((.seq ((.assign 35 ((.lookup ((.temp 2)))))) ((.seq ((.assign 34 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.longMul 32 33 34 35)))))) ((.seq ((.set ((.temp 2)) ((.var 32)))) ((.set ((.temp 0)) ((.var 33)))))))))))) ((.seq ((.seq ((.assign 40 ((.const 0)))) ((.seq ((.assign 39 ((.lookup ((.temp 1)))))) ((.seq ((.assign 38 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.addCarry 37 38 39 40)))))) ((.seq ((.set ((.temp 0)) ((.var 37)))) ((.set ((.temp 4)) ((.var 40)))))))))))))) ((.seq ((.seq ((.assign 45 ((.lookup ((.temp 4)))))) ((.seq ((.assign 44 ((.const 0)))) ((.seq ((.assign 43 ((.lookup ((.temp 2)))))) ((.seq ((.inst ((.arith ((.addCarry 42 43 44 45)))))) ((.seq ((.set ((.temp 2)) ((.var 42)))) ((.set ((.temp 4)) ((.var 45)))))))))))))) ((.seq .skip .skip)))))))) ((.seq ((.seq ((.assign 46 ((.lookup ((.temp 12)))))) ((.set ((.temp 1)) ((.var 46)))))) fragment42)))))) =>
      matches_fragment42 fragment42
  | _ => false

private def matches_fragment44 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.seq ((.assign 17 ((.lookup ((.temp 2)))))) ((.seq ((.assign 16 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.longMul 14 15 16 17)))))) ((.seq ((.set ((.temp 2)) ((.var 14)))) ((.set ((.temp 0)) ((.var 15)))))))))))) ((.seq ((.seq ((.assign 22 ((.const 0)))) ((.seq ((.assign 21 ((.lookup ((.temp 1)))))) ((.seq ((.assign 20 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.addCarry 19 20 21 22)))))) ((.seq ((.set ((.temp 0)) ((.var 19)))) ((.set ((.temp 4)) ((.var 22)))))))))))))) ((.seq ((.seq ((.assign 27 ((.lookup ((.temp 4)))))) ((.seq ((.assign 26 ((.const 0)))) ((.seq ((.assign 25 ((.lookup ((.temp 2)))))) ((.seq ((.inst ((.arith ((.addCarry 24 25 26 27)))))) ((.seq ((.set ((.temp 2)) ((.var 24)))) ((.set ((.temp 4)) ((.var 27)))))))))))))) ((.seq .skip .skip)))))))) ((.seq ((.seq ((.assign 28 ((.lookup ((.temp 12)))))) ((.set ((.temp 1)) ((.var 28)))))) ((.seq ((.seq ((.assign 29 ((.lookup ((.temp 2)))))) ((.set ((.temp 12)) ((.var 29)))))) ((.seq ((.seq ((.assign 30 ((.lookup ((.temp 0)))))) ((.set ((.temp 2)) ((.var 30)))))) fragment43)))))))) =>
      matches_fragment43 fragment43
  | _ => false

private def matches_fragment45 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 58 ((.reg 59)) ((.seq ((.seq ((.assign 1 ((.lookup ((.temp 12)))))) ((.set ((.temp 0)) ((.var 1)))))) ((.seq ((.seq ((.assign 2 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 3 ((.load ((.var 2)))))) ((.set ((.temp 3)) ((.var 3)))))))) ((.seq ((.seq ((.assign 4 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 4)))))) ((.seq ((.seq ((.assign 9 ((.lookup ((.temp 0)))))) ((.seq ((.assign 10 ((.lookup ((.temp 3)))))) ((.ite .equal 9 ((.reg 10)) .skip ((.seq ((.seq ((.assign 5 ((.const 1)))) ((.set ((.temp 8)) ((.var 5)))))) ((.seq ((.assign 7 ((.lookup ((.temp 3)))))) ((.seq ((.assign 8 ((.lookup ((.temp 0)))))) ((.ite .lower 7 ((.reg 8)) .skip ((.seq ((.seq ((.assign 6 ((.const 0)))) ((.set ((.temp 8)) ((.var 6)))))) .skip)))))))))))))))) ((.seq .skip .skip)))))))))) ((.seq ((.seq ((.assign 11 ((.lookup ((.temp 6)))))) ((.set ((.temp 0)) ((.var 11)))))) ((.seq ((.seq ((.assign 12 ((.op .add [(.lookup ((.temp 30))), (.shift .lsl ((.lookup ((.temp 11)))) (.const 3))])))) ((.seq ((.assign 13 ((.load ((.var 12)))))) ((.set ((.temp 2)) ((.var 13)))))))) fragment44)))))) =>
      matches_fragment44 fragment44
  | _ => false

private def matches_fragment46 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.seq ((.assign 25 ((.lookup ((.temp 2)))))) ((.seq ((.assign 24 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.longMul 22 23 24 25)))))) ((.seq ((.set ((.temp 2)) ((.var 22)))) ((.set ((.temp 0)) ((.var 23)))))))))))) ((.seq ((.seq ((.assign 30 ((.const 0)))) ((.seq ((.assign 29 ((.lookup ((.temp 1)))))) ((.seq ((.assign 28 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.addCarry 27 28 29 30)))))) ((.seq ((.set ((.temp 0)) ((.var 27)))) ((.set ((.temp 4)) ((.var 30)))))))))))))) ((.seq ((.seq ((.assign 35 ((.lookup ((.temp 4)))))) ((.seq ((.assign 34 ((.const 0)))) ((.seq ((.assign 33 ((.lookup ((.temp 2)))))) ((.seq ((.inst ((.arith ((.addCarry 32 33 34 35)))))) ((.seq ((.set ((.temp 2)) ((.var 32)))) ((.set ((.temp 4)) ((.var 35)))))))))))))) ((.seq .skip .skip)))))))) ((.seq ((.seq ((.assign 36 ((.lookup ((.temp 2)))))) ((.set ((.temp 3)) ((.var 36)))))) ((.seq ((.seq ((.assign 37 ((.lookup ((.temp 0)))))) ((.set ((.temp 2)) ((.var 37)))))) ((.seq ((.seq ((.assign 38 ((.lookup ((.temp 12)))))) ((.set ((.temp 1)) ((.var 38)))))) ((.seq .skip .skip)))))))))) =>
      true
  | _ => false

private def matches_fragment47 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.seq ((.assign 7 ((.lookup ((.temp 2)))))) ((.seq ((.assign 6 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.longMul 4 5 6 7)))))) ((.seq ((.set ((.temp 2)) ((.var 4)))) ((.set ((.temp 0)) ((.var 5)))))))))))) ((.seq ((.seq ((.assign 12 ((.const 0)))) ((.seq ((.assign 11 ((.lookup ((.temp 1)))))) ((.seq ((.assign 10 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.addCarry 9 10 11 12)))))) ((.seq ((.set ((.temp 0)) ((.var 9)))) ((.set ((.temp 4)) ((.var 12)))))))))))))) ((.seq ((.seq ((.assign 17 ((.lookup ((.temp 4)))))) ((.seq ((.assign 16 ((.const 0)))) ((.seq ((.assign 15 ((.lookup ((.temp 2)))))) ((.seq ((.inst ((.arith ((.addCarry 14 15 16 17)))))) ((.seq ((.set ((.temp 2)) ((.var 14)))) ((.set ((.temp 4)) ((.var 17)))))))))))))) ((.seq .skip .skip)))))))) ((.seq ((.seq ((.assign 18 ((.lookup ((.temp 0)))))) ((.set ((.temp 12)) ((.var 18)))))) ((.seq ((.seq ((.assign 19 ((.lookup ((.temp 6)))))) ((.set ((.temp 0)) ((.var 19)))))) ((.seq ((.seq ((.assign 20 ((.lookup ((.temp 2)))))) ((.set ((.temp 1)) ((.var 20)))))) ((.seq ((.seq ((.assign 21 ((.lookup ((.temp 8)))))) ((.set ((.temp 2)) ((.var 21)))))) fragment46)))))))))) =>
      matches_fragment46 fragment46
  | _ => false

private def matches_fragment48 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 54 ((.reg 55)) ((.seq ((.assign 49 ((.lookup ((.temp 2)))))) ((.seq ((.assign 50 ((.lookup ((.temp 10)))))) ((.ite .equal 49 ((.reg 50)) ((.seq ((.assign 44 ((.lookup ((.temp 1)))))) ((.seq ((.assign 45 ((.lookup ((.temp 9)))))) ((.ite .equal 44 ((.reg 45)) ((.seq ((.seq ((.assign 40 ((.const 0)))) ((.set ((.temp 0)) ((.var 40)))))) .skip)) ((.seq ((.assign 42 ((.lookup ((.temp 9)))))) ((.seq ((.assign 43 ((.lookup ((.temp 1)))))) ((.ite .lower 42 ((.reg 43)) .skip ((.seq ((.seq ((.assign 41 ((.const 0)))) ((.set ((.temp 0)) ((.var 41)))))) .skip)))))))))))))) ((.seq ((.assign 47 ((.lookup ((.temp 10)))))) ((.seq ((.assign 48 ((.lookup ((.temp 2)))))) ((.ite .lower 47 ((.reg 48)) .skip ((.seq ((.seq ((.assign 46 ((.const 0)))) ((.set ((.temp 0)) ((.var 46)))))) .skip)))))))))))))) ((.seq ((.assign 52 ((.lookup ((.temp 11)))))) ((.seq ((.assign 53 ((.lookup ((.temp 3)))))) ((.ite .lower 52 ((.reg 53)) .skip ((.seq ((.seq ((.assign 51 ((.const 0)))) ((.set ((.temp 0)) ((.var 51)))))) .skip)))))))))) =>
      true
  | _ => false

private def matches_fragment49 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 70 ((.const 0)))) ((.seq ((.assign 69 ((.lookup ((.temp 1)))))) ((.seq ((.assign 68 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.addCarry 67 68 69 70)))))) ((.seq ((.set ((.temp 0)) ((.var 67)))) ((.set ((.temp 4)) ((.var 70)))))))))))))) ((.seq ((.seq ((.assign 75 ((.lookup ((.temp 4)))))) ((.seq ((.assign 74 ((.const 0)))) ((.seq ((.assign 73 ((.lookup ((.temp 2)))))) ((.seq ((.inst ((.arith ((.addCarry 72 73 74 75)))))) ((.seq ((.set ((.temp 2)) ((.var 72)))) ((.set ((.temp 4)) ((.var 75)))))))))))))) ((.seq ((.seq ((.assign 80 ((.const 0)))) ((.seq ((.assign 79 ((.lookup ((.temp 3)))))) ((.seq ((.assign 78 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.addCarry 77 78 79 80)))))) ((.seq ((.set ((.temp 0)) ((.var 77)))) ((.set ((.temp 4)) ((.var 80)))))))))))))) ((.seq ((.seq ((.assign 85 ((.lookup ((.temp 4)))))) ((.seq ((.assign 84 ((.const 0)))) ((.seq ((.assign 83 ((.lookup ((.temp 2)))))) ((.seq ((.inst ((.arith ((.addCarry 82 83 84 85)))))) ((.seq ((.set ((.temp 2)) ((.var 82)))) ((.set ((.temp 4)) ((.var 85)))))))))))))) ((.seq .skip .skip)))))))))) =>
      true
  | _ => false

private def matches_fragment50 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.seq ((.assign 87 ((.const 1)))) ((.set ((.temp 1)) ((.var 87)))))) ((.seq ((.assign 97 ((.lookup ((.temp 2)))))) ((.seq ((.assign 98 ((.lookup ((.temp 11)))))) ((.ite .equal 97 ((.reg 98)) ((.seq ((.assign 92 ((.lookup ((.temp 0)))))) ((.seq ((.assign 93 ((.lookup ((.temp 10)))))) ((.ite .equal 92 ((.reg 93)) ((.seq ((.seq ((.assign 88 ((.const 0)))) ((.set ((.temp 1)) ((.var 88)))))) .skip)) ((.seq ((.assign 90 ((.lookup ((.temp 10)))))) ((.seq ((.assign 91 ((.lookup ((.temp 0)))))) ((.ite .lower 90 ((.reg 91)) .skip ((.seq ((.seq ((.assign 89 ((.const 0)))) ((.set ((.temp 1)) ((.var 89)))))) .skip)))))))))))))) ((.seq ((.assign 95 ((.lookup ((.temp 11)))))) ((.seq ((.assign 96 ((.lookup ((.temp 2)))))) ((.ite .lower 95 ((.reg 96)) .skip ((.seq ((.seq ((.assign 94 ((.const 0)))) ((.set ((.temp 1)) ((.var 94)))))) .skip)))))))))))))))) ((.seq ((.assign 99 ((.lookup ((.temp 1)))))) ((.ite .equal 99 ((.imm 0)) ((.seq .skip .skip)) ((.seq .skip ((.call none ((some 55)) [0] none)))))))))) =>
      true
  | _ => false

private def matches_fragment51 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.assign 100 ((.lookup ((.temp 0)))))) ((.ite .equal 100 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 57 ((.lookup ((.temp 6)))))) ((.ite .equal 57 ((.imm 0)) .skip ((.seq ((.seq ((.assign 56 ((.op .sub [(.lookup ((.temp 6))), (.const 1)])))) ((.set ((.temp 6)) ((.var 56)))))) .skip)))))) ((.seq ((.seq ((.assign 58 ((.lookup ((.temp 6)))))) ((.set ((.temp 0)) ((.var 58)))))) ((.seq ((.seq ((.assign 59 ((.const 0)))) ((.set ((.temp 1)) ((.var 59)))))) ((.seq ((.seq ((.assign 60 ((.lookup ((.temp 8)))))) ((.set ((.temp 2)) ((.var 60)))))) ((.seq ((.seq ((.assign 61 ((.lookup ((.temp 1)))))) ((.set ((.temp 3)) ((.var 61)))))) ((.seq ((.seq ((.seq ((.assign 65 ((.lookup ((.temp 2)))))) ((.seq ((.assign 64 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.longMul 62 63 64 65)))))) ((.seq ((.set ((.temp 2)) ((.var 62)))) ((.set ((.temp 0)) ((.var 63)))))))))))) fragment49)) ((.seq ((.seq ((.assign 86 ((.op .add [(.lookup ((.temp 2))), (.const 1)])))) ((.set ((.temp 2)) ((.var 86)))))) fragment50)))))))))))))))))) =>
      matches_fragment49 fragment49 &&
      matches_fragment50 fragment50
  | _ => false

private def matches_fragment52 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.seq ((.assign 9 ((.lookup ((.temp 2)))))) ((.seq ((.assign 8 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.longMul 6 7 8 9)))))) ((.seq ((.set ((.temp 2)) ((.var 6)))) ((.set ((.temp 0)) ((.var 7)))))))))))) ((.seq ((.seq ((.assign 14 ((.const 0)))) ((.seq ((.assign 13 ((.lookup ((.temp 1)))))) ((.seq ((.assign 12 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.addCarry 11 12 13 14)))))) ((.seq ((.set ((.temp 0)) ((.var 11)))) ((.set ((.temp 4)) ((.var 14)))))))))))))) ((.seq ((.seq ((.assign 19 ((.lookup ((.temp 4)))))) ((.seq ((.assign 18 ((.const 0)))) ((.seq ((.assign 17 ((.lookup ((.temp 2)))))) ((.seq ((.inst ((.arith ((.addCarry 16 17 18 19)))))) ((.seq ((.set ((.temp 2)) ((.var 16)))) ((.set ((.temp 4)) ((.var 19)))))))))))))) ((.seq .skip .skip)))))))) ((.seq ((.seq ((.assign 20 ((.lookup ((.temp 2)))))) ((.set ((.temp 1)) ((.var 20)))))) ((.seq ((.seq ((.assign 21 ((.op .add [(.lookup ((.temp 11))), (.const 1)])))) ((.set ((.temp 11)) ((.var 21)))))) ((.seq .skip ((.call none ((some 53)) [0] none)))))))))) =>
      true
  | _ => false

private def matches_fragment53 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 16 ((.const 0)))) ((.seq ((.assign 15 ((.lookup ((.temp 1)))))) ((.seq ((.assign 14 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.addCarry 13 14 15 16)))))) ((.seq ((.set ((.temp 0)) ((.var 13)))) ((.set ((.temp 4)) ((.var 16)))))))))))))) ((.seq ((.seq ((.assign 21 ((.lookup ((.temp 4)))))) ((.seq ((.assign 20 ((.const 0)))) ((.seq ((.assign 19 ((.lookup ((.temp 2)))))) ((.seq ((.inst ((.arith ((.addCarry 18 19 20 21)))))) ((.seq ((.set ((.temp 2)) ((.var 18)))) ((.set ((.temp 4)) ((.var 21)))))))))))))) ((.seq ((.seq ((.assign 26 ((.const 0)))) ((.seq ((.assign 25 ((.lookup ((.temp 3)))))) ((.seq ((.assign 24 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.addCarry 23 24 25 26)))))) ((.seq ((.set ((.temp 0)) ((.var 23)))) ((.set ((.temp 4)) ((.var 26)))))))))))))) ((.seq ((.seq ((.assign 31 ((.lookup ((.temp 4)))))) ((.seq ((.assign 30 ((.const 0)))) ((.seq ((.assign 29 ((.lookup ((.temp 2)))))) ((.seq ((.inst ((.arith ((.addCarry 28 29 30 31)))))) ((.seq ((.set ((.temp 2)) ((.var 28)))) ((.set ((.temp 4)) ((.var 31)))))))))))))) ((.seq .skip .skip)))))))))) =>
      true
  | _ => false

private def matches_fragment54 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 37 ((.reg 38)) ((.seq ((.seq ((.assign 1 ((.lookup ((.temp 1)))))) ((.seq ((.assign 2 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 2)) 1)))))) ((.seq ((.seq ((.assign 3 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 3)))))) ((.seq .skip .skip)))))) ((.seq ((.seq ((.assign 4 ((.op .add [(.lookup ((.temp 31))), (.shift .lsl ((.lookup ((.temp 11)))) (.const 3))])))) ((.seq ((.assign 5 ((.load ((.var 4)))))) ((.set ((.temp 2)) ((.var 5)))))))) ((.seq ((.seq ((.assign 6 ((.lookup ((.temp 8)))))) ((.set ((.temp 0)) ((.var 6)))))) ((.seq ((.seq ((.assign 7 ((.const 0)))) ((.set ((.temp 3)) ((.var 7)))))) ((.seq ((.seq ((.seq ((.assign 11 ((.lookup ((.temp 2)))))) ((.seq ((.assign 10 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.longMul 8 9 10 11)))))) ((.seq ((.set ((.temp 2)) ((.var 8)))) ((.set ((.temp 0)) ((.var 9)))))))))))) fragment53)) ((.seq ((.seq ((.assign 32 ((.lookup ((.temp 0)))))) ((.seq ((.assign 33 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 33)) 32)))))) ((.seq ((.seq ((.assign 34 ((.lookup ((.temp 2)))))) ((.set ((.temp 1)) ((.var 34)))))) ((.seq ((.seq ((.assign 35 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 35)))))) ((.seq ((.seq ((.assign 36 ((.op .add [(.lookup ((.temp 11))), (.const 1)])))) ((.set ((.temp 11)) ((.var 36)))))) ((.seq .skip ((.call none ((some 52)) [0] none)))))))))))))))))))))) =>
      matches_fragment53 fragment53
  | _ => false

private def matches_fragment55 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 11 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 1)))))) ((.seq ((.seq ((.assign 2 ((.op .add [(.lookup ((.temp 31))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 3 ((.load ((.var 2)))))) ((.set ((.temp 0)) ((.var 3)))))))) ((.seq ((.seq ((.seq ((.assign 8 ((.lookup ((.temp 9)))))) ((.seq ((.assign 7 ((.lookup ((.temp 0)))))) ((.seq ((.assign 6 ((.lookup ((.temp 2)))))) ((.seq ((.mustTerminate ((.seq ((.call ((some ([4], (live42, .ln), .skip, 50, 2))) ((some 23)) [6, 7, 8] none)) ((.assign 5 ((.lookup ((.temp 28)))))))))) ((.seq ((.set ((.temp 0)) ((.var 4)))) ((.set ((.temp 2)) ((.var 5)))))))))))))) .skip)) ((.seq ((.seq ((.assign 9 ((.lookup ((.temp 0)))))) ((.seq ((.assign 10 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 10)) 9)))))) ((.seq .skip ((.call none ((some 50)) [0] none)))))))))))))) =>
      decide (live42 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment56 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 10 ((.imm 0)) ((.seq ((.seq ((.assign 1 ((.op .add [(.lookup ((.temp 10))), (.lookup ((.temp 9)))])))) ((.set ((.temp 10)) ((.var 1)))))) ((.seq .skip .skip)))) ((.seq ((.seq ((.assign 2 ((.op .sub [(.lookup ((.temp 7))), (.const 1)])))) ((.set ((.temp 7)) ((.var 2)))))) ((.seq ((.seq ((.assign 3 ((.op .add [(.lookup ((.temp 31))), (.shift .lsl ((.lookup ((.temp 12)))) (.const 3))])))) ((.seq ((.assign 4 ((.load ((.var 3)))))) ((.set ((.temp 8)) ((.var 4)))))))) ((.seq ((.seq ((.assign 5 ((.op .add [(.lookup ((.temp 12))), (.const 1)])))) ((.set ((.temp 12)) ((.var 5)))))) ((.seq ((.seq ((.assign 6 ((.const 0)))) ((.set ((.temp 11)) ((.var 6)))))) ((.seq ((.seq ((.assign 7 ((.lookup ((.temp 11)))))) ((.set ((.temp 1)) ((.var 7)))))) ((.seq ((.call ((some ([8], (live43, .ln), .skip, 47, 2))) ((some 48)) [] none)) ((.seq ((.seq ((.assign 9 ((.op .sub [(.lookup ((.temp 10))), (.lookup ((.temp 9)))])))) ((.set ((.temp 10)) ((.var 9)))))) ((.seq .skip ((.call none ((some 47)) [0] none)))))))))))))))))))) =>
      decide (live43 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment57 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 17 ((.const 0)))) ((.seq ((.assign 16 ((.lookup ((.temp 1)))))) ((.seq ((.assign 15 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.addCarry 14 15 16 17)))))) ((.seq ((.set ((.temp 0)) ((.var 14)))) ((.set ((.temp 4)) ((.var 17)))))))))))))) ((.seq ((.seq ((.assign 22 ((.lookup ((.temp 4)))))) ((.seq ((.assign 21 ((.const 0)))) ((.seq ((.assign 20 ((.lookup ((.temp 2)))))) ((.seq ((.inst ((.arith ((.addCarry 19 20 21 22)))))) ((.seq ((.set ((.temp 2)) ((.var 19)))) ((.set ((.temp 4)) ((.var 22)))))))))))))) ((.seq ((.seq ((.assign 27 ((.const 0)))) ((.seq ((.assign 26 ((.lookup ((.temp 3)))))) ((.seq ((.assign 25 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.addCarry 24 25 26 27)))))) ((.seq ((.set ((.temp 0)) ((.var 24)))) ((.set ((.temp 4)) ((.var 27)))))))))))))) ((.seq ((.seq ((.assign 32 ((.lookup ((.temp 4)))))) ((.seq ((.assign 31 ((.const 0)))) ((.seq ((.assign 30 ((.lookup ((.temp 2)))))) ((.seq ((.inst ((.arith ((.addCarry 29 30 31 32)))))) ((.seq ((.set ((.temp 2)) ((.var 29)))) ((.set ((.temp 4)) ((.var 32)))))))))))))) ((.seq .skip .skip)))))))))) =>
      true
  | _ => false

private def matches_fragment58 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 6 ((.op .add [(.lookup ((.temp 30))), (.shift .lsl ((.lookup ((.temp 11)))) (.const 3))])))) ((.seq ((.assign 7 ((.load ((.var 6)))))) ((.set ((.temp 2)) ((.var 7)))))))) ((.seq ((.seq ((.assign 8 ((.lookup ((.temp 8)))))) ((.set ((.temp 0)) ((.var 8)))))) ((.seq ((.seq ((.seq ((.assign 12 ((.lookup ((.temp 2)))))) ((.seq ((.assign 11 ((.lookup ((.temp 0)))))) ((.seq ((.inst ((.arith ((.longMul 9 10 11 12)))))) ((.seq ((.set ((.temp 2)) ((.var 9)))) ((.set ((.temp 0)) ((.var 10)))))))))))) fragment57)) ((.seq ((.seq ((.assign 33 ((.lookup ((.temp 0)))))) ((.seq ((.assign 34 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 34)) 33)))))) ((.seq ((.seq ((.assign 35 ((.lookup ((.temp 2)))))) ((.set ((.temp 1)) ((.var 35)))))) ((.seq ((.seq ((.assign 36 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 36)))))) ((.seq ((.seq ((.assign 37 ((.op .add [(.lookup ((.temp 11))), (.const 1)])))) ((.set ((.temp 11)) ((.var 37)))))) ((.seq .skip ((.call none ((some 48)) [0] none)))))))))))))))))) =>
      matches_fragment57 fragment57
  | _ => false

private def matches_fragment59 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 13 ((.imm 1)) ((.seq ((.seq ((.assign 1 ((.const 0)))) ((.set ((.temp 1)) ((.var 1)))))) .skip)) ((.seq ((.seq ((.assign 2 ((.op .sub [(.lookup ((.temp 1))), (.const 1)])))) ((.set ((.temp 1)) ((.var 2)))))) ((.seq ((.seq ((.assign 3 ((.op .add [(.lookup ((.temp 31))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 4 ((.load ((.var 3)))))) ((.set ((.temp 8)) ((.var 4)))))))) ((.seq ((.seq ((.assign 9 ((.lookup ((.temp 3)))))) ((.seq ((.assign 8 ((.lookup ((.temp 9)))))) ((.seq ((.assign 8 ((.op .xor [(.var 8), (.const 18446744073709551615)])))) ((.seq ((.assign 7 ((.lookup ((.temp 8)))))) ((.seq ((.inst ((.arith ((.addCarry 6 7 8 9)))))) ((.seq ((.set ((.temp 8)) ((.var 6)))) ((.set ((.temp 3)) ((.var 9)))))))))))))))) ((.seq ((.seq ((.assign 10 ((.lookup ((.temp 8)))))) ((.seq ((.assign 11 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 11)) 10)))))) ((.seq ((.seq ((.assign 12 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 12)))))) ((.call none ((some 44)) [0] none)))))))))))))) =>
      true
  | _ => false

private def matches_fragment60 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 3 ((.op .add [(.lookup ((.temp 31))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 4 ((.load ((.var 3)))))) ((.set ((.temp 8)) ((.var 4)))))))) ((.seq ((.seq ((.assign 5 ((.op .add [(.lookup ((.temp 30))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 6 ((.load ((.var 5)))))) ((.set ((.temp 9)) ((.var 6)))))))) ((.seq ((.seq ((.assign 11 ((.lookup ((.temp 3)))))) ((.seq ((.assign 10 ((.lookup ((.temp 9)))))) ((.seq ((.assign 10 ((.op .xor [(.var 10), (.const 18446744073709551615)])))) ((.seq ((.assign 9 ((.lookup ((.temp 8)))))) ((.seq ((.inst ((.arith ((.addCarry 8 9 10 11)))))) ((.seq ((.set ((.temp 8)) ((.var 8)))) ((.set ((.temp 3)) ((.var 11)))))))))))))))) ((.seq ((.seq ((.assign 12 ((.lookup ((.temp 8)))))) ((.seq ((.assign 13 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 13)) 12)))))) ((.seq ((.seq ((.assign 14 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 14)))))) ((.call none ((some 43)) [0] none)))))))))))) =>
      true
  | _ => false

private def matches_fragment61 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 12 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 1)))))) ((.seq ((.seq ((.assign 2 ((.op .add [(.lookup ((.temp 31))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 3 ((.load ((.var 2)))))) ((.set ((.temp 8)) ((.var 3)))))))) ((.seq ((.seq ((.assign 4 ((.op .add [(.lookup ((.temp 30))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 5 ((.load ((.var 4)))))) ((.set ((.temp 9)) ((.var 5)))))))) ((.seq ((.assign 10 ((.lookup ((.temp 8)))))) ((.seq ((.assign 11 ((.lookup ((.temp 9)))))) ((.ite .equal 10 ((.reg 11)) ((.seq .skip ((.call none ((some 42)) [0] none)))) ((.seq ((.assign 8 ((.lookup ((.temp 8)))))) ((.seq ((.assign 9 ((.lookup ((.temp 9)))))) ((.ite .lower 8 ((.reg 9)) ((.seq ((.seq ((.assign 6 ((.const 1)))) ((.set ((.temp 10)) ((.var 6)))))) ((.seq .skip .skip)))) ((.seq ((.seq ((.assign 7 (.const 2))) ((.set ((.temp 10)) ((.var 7)))))) ((.seq .skip .skip)))))))))))))))))))))))) =>
      true
  | _ => false

private def matches_fragment62 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 13 ((.imm 1)) ((.seq ((.seq ((.assign 1 ((.const 0)))) ((.set ((.temp 1)) ((.var 1)))))) .skip)) ((.seq ((.seq ((.assign 2 ((.op .sub [(.lookup ((.temp 1))), (.const 1)])))) ((.set ((.temp 1)) ((.var 2)))))) ((.seq ((.seq ((.assign 3 ((.op .add [(.lookup ((.temp 31))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 4 ((.load ((.var 3)))))) ((.set ((.temp 8)) ((.var 4)))))))) ((.seq ((.seq ((.assign 9 ((.lookup ((.temp 3)))))) ((.seq ((.assign 8 ((.lookup ((.temp 9)))))) ((.seq ((.assign 7 ((.lookup ((.temp 8)))))) ((.seq ((.inst ((.arith ((.addCarry 6 7 8 9)))))) ((.seq ((.set ((.temp 8)) ((.var 6)))) ((.set ((.temp 3)) ((.var 9)))))))))))))) ((.seq ((.seq ((.assign 10 ((.lookup ((.temp 8)))))) ((.seq ((.assign 11 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 11)) 10)))))) ((.seq ((.seq ((.assign 12 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 12)))))) ((.call none ((some 41)) [0] none)))))))))))))) =>
      true
  | _ => false

private def matches_fragment63 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 3 ((.op .add [(.lookup ((.temp 31))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 4 ((.load ((.var 3)))))) ((.set ((.temp 8)) ((.var 4)))))))) ((.seq ((.seq ((.assign 5 ((.op .add [(.lookup ((.temp 30))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 6 ((.load ((.var 5)))))) ((.set ((.temp 9)) ((.var 6)))))))) ((.seq ((.seq ((.assign 11 ((.lookup ((.temp 3)))))) ((.seq ((.assign 10 ((.lookup ((.temp 9)))))) ((.seq ((.assign 9 ((.lookup ((.temp 8)))))) ((.seq ((.inst ((.arith ((.addCarry 8 9 10 11)))))) ((.seq ((.set ((.temp 8)) ((.var 8)))) ((.set ((.temp 3)) ((.var 11)))))))))))))) ((.seq ((.seq ((.assign 12 ((.lookup ((.temp 8)))))) ((.seq ((.assign 13 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 13)) 12)))))) ((.seq ((.seq ((.assign 14 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 14)))))) ((.call none ((some 40)) [0] none)))))))))))) =>
      true
  | _ => false

private def matches_fragment64 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.ite .test 24 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live50, .ln))))))) ((.seq ((.move 0 [(1, 24)])) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live51, live52))) .skip)))) .skip)))))))) ((.mustTerminate ((.call ((some ([26], (live53, live54), .skip, 62, 5))) ((some 10)) [24, 22] none)))))))))) ((.seq ((.seq ((.set .globals ((.var 26)))) ((.seq ((.set .globReal ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 26)) (.const 5))])))) ((.assign 28 (.const 2))))))) ((.seq ((.assign 30 ((.const 4)))) ((.seq ((.seq ((.inst ((.arith ((.subOverflow 1 12 30 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 12), (.var 30)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live55, live56), .skip, 62, 6))) ((some 14)) [12, 30] none)))))) ((.move 2 [(32, 1)])))))))) ((.call none ((some 63)) [0, 26, 4, 32] none)))))))))) =>
      decide (live50 = Flapjack.sptListInsert [0] .ln) &&
      decide (live51 = Flapjack.sptListInsert [0] .ln) &&
      decide (live52 = Flapjack.sptListInsert [4, 12, 22, 24] .ln) &&
      decide (live53 = Flapjack.sptListInsert [0] .ln) &&
      decide (live54 = Flapjack.sptListInsert [4, 12] .ln) &&
      decide (live55 = Flapjack.sptListInsert [0] .ln) &&
      decide (live56 = Flapjack.sptListInsert [4, 26] .ln)
  | _ => false

private def matches_fragment65 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.assign 14 ((.const 0)))) ((.seq ((.seq ((.store ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 14)) (.const 1))])])) 10)) ((.assign 16 (.const 2))))) ((.seq ((.seq ((.assign 1 ((.var 10)))) ((.seq ((.assign 3 ((.var 12)))) ((.seq ((.assign 5 ((.op .or [(.var 1), (.var 3)])))) ((.seq ((.ite .test 5 ((.imm 1)) .skip ((.seq ((.mustTerminate ((.call ((some ([1], (live46, live47), .skip, 62, 3))) ((some 19)) [1, 3] none)))) ((.assign 3 ((.const 1)))))))) ((.ite .less 1 ((.reg 3)) ((.assign 18 (.const 18))) ((.assign 18 (.const 2))))))))))))) ((.ite .equal 18 ((.imm 18)) ((.return 0 [16])) ((.seq ((.assign 22 ((.const 0)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 10 10 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 10), (.var 10)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live48, live49), .skip, 62, 4))) ((some 13)) [10, 10] none)))))) ((.move 2 [(24, 1)])))))))) fragment64)))))))))))) =>
      decide (live46 = Flapjack.sptListInsert [0] .ln) &&
      decide (live47 = Flapjack.sptListInsert [4, 10, 12, 16] .ln) &&
      decide (live48 = Flapjack.sptListInsert [0] .ln) &&
      decide (live49 = Flapjack.sptListInsert [4, 12, 22] .ln) &&
      matches_fragment64 fragment64
  | _ => false

private def matches_fragment66 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.store ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 6)) (.const 1))])])) 8)) ((.assign 10 (.const 2))))) ((.seq ((.assign 12 ((.const 0)))) ((.seq ((.seq ((.assign 1 ((.var 6)))) ((.seq ((.assign 3 ((.var 12)))) ((.seq ((.assign 5 ((.op .and [(.var 1), (.var 3)])))) ((.seq ((.ite .test 5 ((.imm 1)) .skip ((.ite .equal 1 ((.reg 3)) .skip ((.seq ((.mustTerminate ((.call ((some ([1], (live57, live58), .skip, 63, 2))) ((some 21)) [1, 3] none)))) ((.assign 3 ((.const 1)))))))))) ((.ite .equal 1 ((.reg 3)) ((.assign 14 (.const 18))) ((.assign 14 (.const 2))))))))))))) ((.ite .equal 14 ((.imm 18)) ((.return 0 [10])) ((.seq ((.assign 18 ((.const 4)))) ((.seq ((.seq ((.inst ((.arith ((.subOverflow 1 6 18 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 6), (.var 18)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live59, live60), .skip, 63, 3))) ((some 14)) [6, 18] none)))))) ((.move 2 [(20, 1)])))))))) ((.call none ((some 63)) [0, 2, 4, 20] none)))))))))))))) =>
      decide (live57 = Flapjack.sptListInsert [0] .ln) &&
      decide (live58 = Flapjack.sptListInsert [2, 4, 6, 10] .ln) &&
      decide (live59 = Flapjack.sptListInsert [0] .ln) &&
      decide (live60 = Flapjack.sptListInsert [2, 4] .ln)
  | _ => false

private def matches_fragment67 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.ite .test 4 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live61, .ln))))))) ((.seq ((.move 0 [(1, 4)])) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live62, live63))) .skip)))) .skip)))))))) ((.mustTerminate ((.call ((some ([6], (live64, .ln), .skip, 64, 2))) ((some 10)) [4, 2] none)))))))))) ((.seq ((.assign 8 ((.const 4)))) ((.seq ((.assign 10 ((.const 0)))) ((.seq ((.seq ((.store ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 10)) (.const 1))])])) 8)) ((.assign 12 (.const 2))))) ((.seq ((.seq ((.set .globals ((.var 6)))) ((.seq ((.set .globReal ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))])))) ((.assign 14 (.const 2))))))) ((.seq ((.call ((some ([18], (live65, .ln), .skip, 64, 3))) ((some 76)) [] ((some (16, (.move 0 [(18, 16)]), 64, 4))))) ((.return 0 [18])))))))))))))) =>
      decide (live61 = Flapjack.sptListInsert [0] .ln) &&
      decide (live62 = Flapjack.sptListInsert [0] .ln) &&
      decide (live63 = Flapjack.sptListInsert [2, 4] .ln) &&
      decide (live64 = Flapjack.sptListInsert [0] .ln) &&
      decide (live65 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment68 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.assign 14 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 12)) (.const 1))])])))))) ((.seq ((.seq ((.assign 1 ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.op .add [(.const 8), (.shift .lsr ((.var 4)) (.const 2))])])))) ((.seq ((.assign 3 ((.shift .lsr ((.var 14)) (.const 2))))) ((.seq ((.inst ((.mem .store8 3 ((.addr 1 0)))))) ((.assign 16 (.const 2))))))))) ((.seq ((.assign 18 ((.const 4)))) ((.seq ((.assign 20 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 18)) (.const 1))])])))))) ((.seq ((.assign 22 ((.const 4)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 22 4 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 22), (.var 4)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live68, live69), .skip, 66, 2))) ((some 13)) [22, 4] none)))))) ((.move 2 [(24, 1)])))))))) ((.call none ((some 66)) [0, 20, 24, 6] none)))))))))))))) =>
      decide (live68 = Flapjack.sptListInsert [0] .ln) &&
      decide (live69 = Flapjack.sptListInsert [6, 20] .ln)
  | _ => false

private def matches_fragment69 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 24)) ((.seq .skip ((.seq ((.assign 1 ((.const 24)))) ((.seq ((.alloc 1 (live72, live73))) .skip)))))) .skip)))) ((.seq ((.seq ((.assign 1 ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.op .add [(.const 8), (.shift .lsr ((.var 14)) (.const 2))])])))) ((.seq ((.inst ((.mem .load8 3 ((.addr 1 0)))))) ((.assign 16 ((.shift .lsl ((.var 3)) (.const 2))))))))) ((.seq ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 3 ((.const 562949953421315)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 16)) ((.seq ((.store ((.op .add [(.var 1), (.const 16)])) 2)) .skip)))))) ((.seq ((.assign 18 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 5)])))) ((.set .nextFree ((.op .add [(.var 1), (.const 24)])))))))))))) ((.call none ((some 67)) [0, 18, 14, 6] none)))))))) =>
      decide (live72 = Flapjack.sptListInsert [0] .ln) &&
      decide (live73 = Flapjack.sptListInsert [2, 6, 14] .ln)
  | _ => false

private def matches_fragment70 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.ite .equal 6 ((.imm 18)) ((.return 0 [4])) ((.seq ((.assign 10 ((.const 4)))) ((.seq ((.assign 12 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 10)) (.const 1))])])))))) ((.seq ((.assign 14 ((.const 0)))) ((.seq ((.assign 16 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 14)) (.const 1))])])))))) ((.seq ((.assign 18 ((.shift .lsl ((.op .sub [(.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 16)) (.const 5))])))) (.const 45)), (.const 8)])) (.const 2))))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 18 4 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 18), (.var 4)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live74, live75), .skip, 68, 2))) ((some 13)) [18, 4] none)))))) ((.move 2 [(20, 1)])))))))) ((.call none ((some 68)) [0, 12, 20] none)))))))))))))))) =>
      decide (live74 = Flapjack.sptListInsert [0] .ln) &&
      decide (live75 = Flapjack.sptListInsert [12] .ln)
  | _ => false

private def matches_fragment71 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.assign 14 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 12)) (.const 1))])])))))) ((.seq ((.assign 16 ((.shift .lsl ((.op .sub [(.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 14)) (.const 5))])))) (.const 45)), (.const 8)])) (.const 2))))) ((.seq ((.assign 18 ((.const 0)))) ((.seq ((.mustTerminate ((.call ((some ([20], (live76, live77), .skip, 69, 2))) ((some 25)) [14, 18, 16, 6, 4] none)))) ((.seq ((.assign 22 ((.const 4)))) ((.seq ((.assign 24 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 22)) (.const 1))])])))))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 16 4 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 16), (.var 4)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live78, live79), .skip, 69, 3))) ((some 13)) [16, 4] none)))))) ((.move 2 [(26, 1)])))))))) ((.call none ((some 69)) [0, 24, 26, 6] none)))))))))))))))) =>
      decide (live76 = Flapjack.sptListInsert [0] .ln) &&
      decide (live77 = Flapjack.sptListInsert [2, 4, 6, 16] .ln) &&
      decide (live78 = Flapjack.sptListInsert [0] .ln) &&
      decide (live79 = Flapjack.sptListInsert [6, 24] .ln)
  | _ => false

private def matches_fragment72 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.ite .equal 6 ((.imm 0)) ((.assign 8 (.const 18))) ((.assign 8 (.const 2))))) ((.ite .equal 8 ((.imm 18)) ((.seq ((.assign 10 (.const 2))) ((.seq ((.assign 12 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 8)])))))) ((.seq ((.call ((some ([14], (live80, live81), .skip, 72, 2))) none [10, 4, 12] none)) ((.seq ((.seq ((.assign 1 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 3 ((.const 281474976710715)))) ((.seq ((.store ((.var 1)) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 14)) ((.assign 16 (.const 2))))))))))) ((.return 0 [14])))))))))) ((.seq ((.assign 20 (.const 2))) ((.seq ((.call ((some ([22], (live82, live83), .skip, 72, 3))) ((some 72)) [20, 4] none)) ((.seq ((.seq ((.assign 1 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 3 ((.const 281474976710715)))) ((.seq ((.store ((.var 1)) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 22)) ((.assign 24 (.const 2))))))))))) ((.return 0 [22])))))))))))) =>
      decide (live80 = Flapjack.sptListInsert [0] .ln) &&
      decide (live81 = Flapjack.sptListInsert [2] .ln) &&
      decide (live82 = Flapjack.sptListInsert [0] .ln) &&
      decide (live83 = Flapjack.sptListInsert [2] .ln)
  | _ => false

private def matches0 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (7, 4, (.ite .equal 2 ((.imm 0)) ((.seq ((.assign 6 ((.op .add [(.var 6), (.const 2)])))) ((.return 0 [6])))) ((.seq ((.ite .test 2 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live0, .ln))))))) ((.seq ((.assign 1 ((.var 2)))) fragment0))))), 0) =>
      decide (live0 = Flapjack.sptListInsert [0] .ln) &&
      matches_fragment0 fragment0
  | _ => false

private def matches1 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (8, 6, (.seq ((.store ((.var 2)) 10)) ((.seq ((.assign 2 ((.op .add [(.var 2), (.const 8)])))) ((.ite .equal 6 ((.imm 0)) ((.seq ((.set .nextFree ((.var 2)))) ((.return 0 [8])))) ((.seq ((.assign 4 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 10 ((.load ((.op .add [(.var 4), (.const 8)])))))) ((.seq ((.assign 4 ((.load ((.op .add [(.var 4), (.const 16)])))))) ((.seq ((.assign 6 ((.op .sub [(.var 6), (.const 4)])))) ((.call none ((some 8)) [0, 2, 4, 6, 8, 10] none))))))))))))))), 0) =>
      true
  | _ => false

private def matches2 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (9, 4, (.seq ((.ite .test 2 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live3, .ln))))))) ((.seq ((.assign 1 ((.shift .lsr ((.op .add [(.shift .lsr ((.var 2)) (.const 2)), (.const 8)])) (.const 1))))) fragment2))), 0) =>
      decide (live3 = Flapjack.sptListInsert [0] .ln) &&
      matches_fragment2 fragment2
  | _ => false

private def matches3 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (10, 3, (.seq ((.assign 1 ((.shift .lsl ((.op .add [(.shift .lsr ((.var 2)) (.const 2)), (.const 1)])) (.const 3))))) ((.seq ((.set .triggerGC ((.op .sub [(.lookup .triggerGC), (.var 1)])))) ((.seq ((.assign 1 ((.op .sub [(.lookup .endOfHeap), (.var 1)])))) ((.seq ((.set .endOfHeap ((.var 1)))) ((.seq ((.assign 3 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 1)])))) ((.seq ((.assign 5 ((.op .or [(.shift .lsl ((.var 2)) (.const 46)), (.const 11)])))) ((.seq ((.store ((.var 1)) 5)) ((.call none ((some 11)) [0, 1, 4, 2, 3] none))))))))))))))), 0) =>
      true
  | _ => false

private def matches4 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (11, 5, (.ite .equal 6 ((.imm 0)) ((.return 0 [8])) ((.seq ((.assign 2 ((.op .add [(.var 2), (.const 8)])))) ((.seq ((.store ((.var 2)) 4)) ((.seq ((.assign 6 ((.op .sub [(.var 6), (.const 4)])))) ((.call none ((some 11)) [0, 2, 4, 6, 8] none))))))))), 0) =>
      true
  | _ => false

private def matches5 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (12, 4, (.seq ((.assign 1 ((.const 4)))) ((.seq ((.ite .equal 2 ((.imm 0)) .skip ((.ite .test 2 ((.imm 1)) ((.assign 1 ((.op .add [(.var 1), (.const 4)])))) ((.assign 1 ((.op .add [(.var 1), (.shift .lsl ((.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) (.const 48))) (.const 2))])))))))) ((.seq ((.ite .equal 4 ((.imm 0)) .skip ((.ite .test 4 ((.imm 1)) ((.assign 1 ((.op .add [(.var 1), (.const 4)])))) ((.assign 1 ((.op .add [(.var 1), (.shift .lsl ((.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) (.const 48))) (.const 2))])))))))) ((.seq ((.set ((.temp 29)) ((.var 1)))) fragment6))))))), 0) =>
      matches_fragment6 fragment6
  | _ => false

private def matches6 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (13, 3, (.seq ((.assign 6 ((.const 0)))) ((.call none ((some 12)) [0, 2, 4, 6] none))), 0) =>
      true
  | _ => false

private def matches7 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (14, 3, (.seq ((.assign 6 ((.const 4)))) ((.call none ((some 12)) [0, 2, 4, 6] none))), 0) =>
      true
  | _ => false

private def matches8 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (15, 3, (.seq ((.assign 6 ((.const 16)))) ((.call none ((some 12)) [0, 2, 4, 6] none))), 0) =>
      true
  | _ => false

private def matches9 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (16, 3, (.seq ((.assign 6 ((.const 20)))) ((.call none ((some 12)) [0, 2, 4, 6] none))), 0) =>
      true
  | _ => false

private def matches10 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (17, 3, (.seq ((.assign 6 ((.const 24)))) ((.call none ((some 12)) [0, 2, 4, 6] none))), 0) =>
      true
  | _ => false

private def matches11 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (18, 4, (.ite .equal 2 ((.imm 0)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) ((.seq ((.assign 8 ((.load ((.var 4)))))) ((.seq ((.assign 9 ((.load ((.var 6)))))) ((.ite .equal 8 ((.reg 9)) ((.seq ((.assign 2 ((.op .sub [(.var 2), (.const 1)])))) ((.seq ((.assign 4 ((.op .sub [(.var 4), (.const 8)])))) ((.seq ((.assign 6 ((.op .sub [(.var 6), (.const 8)])))) ((.call none ((some 18)) [0, 2, 4, 6] none)))))))) ((.ite .lower 8 ((.reg 9)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2]))))))))))))), 0) =>
      true
  | _ => false

private def matches12 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (19, 3, (.ite .test 2 ((.imm 1)) ((.seq ((.assign 1 ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))))) ((.ite .test 1 ((.imm 16)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))))))) ((.ite .test 4 ((.imm 1)) ((.seq ((.assign 1 ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))))) ((.ite .test 1 ((.imm 16)) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))))))) ((.seq ((.assign 11 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 1 ((.load ((.var 11)))))) fragment7))))))), 0) =>
      matches_fragment7 fragment7
  | _ => false

private def matches13 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (20, 4, (.seq ((.ite .equal 2 ((.imm 0)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 1 ((.load ((.var 4)))))) ((.seq ((.assign 3 ((.load ((.var 6)))))) ((.seq ((.call ((some ([5], (live10, .ln), .skip, 20, 2))) ((some 21)) [1, 3] none)) ((.seq ((.ite .equal 5 ((.imm 1)) .skip ((.return 0 [5])))) ((.seq ((.assign 2 ((.op .sub [(.var 2), (.const 1)])))) ((.seq ((.assign 4 ((.op .add [(.var 4), (.const 8)])))) ((.seq ((.assign 6 ((.op .add [(.var 6), (.const 8)])))) ((.call none ((some 20)) [0, 2, 4, 6] none))))))))))))))))), 0) =>
      decide (live10 = Flapjack.sptListInsert [0, 2, 4, 6] .ln)
  | _ => false

private def matches14 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (21, 3, (.seq ((.ite .equal 2 ((.reg 4)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 1 ((.op .and [(.var 2), (.var 4)])))) ((.seq ((.ite .test 1 ((.imm 1)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 20 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 40 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 21 ((.load ((.var 20)))))) ((.seq ((.assign 41 ((.load ((.var 40)))))) fragment8))))))))))))), 0) =>
      matches_fragment8 fragment8
  | _ => false

private def matches15 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (22, 7, (.ite .test 2 ((.reg 2)) ((.seq ((.set ((.temp 28)) ((.var 10)))) ((.return 0 [8])))) ((.seq ((.assign 6 ((.op .or [(.shift .lsr ((.var 6)) (.const 1)), (.shift .lsl ((.var 4)) (.const 63))])))) ((.seq ((.assign 4 ((.shift .lsr ((.var 4)) (.const 1))))) ((.seq ((.assign 8 ((.shift .lsl ((.var 8)) (.const 1))))) ((.seq ((.assign 2 ((.op .sub [(.var 2), (.const 1)])))) ((.seq ((.ite .lower 12 ((.reg 4)) ((.call none ((some 22)) [0, 2, 4, 6, 8, 10, 12] none)) .skip)) ((.seq ((.ite .equal 12 ((.reg 4)) ((.ite .lower 10 ((.reg 6)) ((.call none ((some 22)) [0, 2, 4, 6, 8, 10, 12] none)) .skip)) .skip)) ((.seq ((.assign 8 ((.op .add [(.var 8), (.const 1)])))) ((.seq ((.assign 16 ((.op .xor [(.var 6), (.const 18446744073709551615)])))) ((.seq ((.assign 14 ((.op .xor [(.var 4), (.const 18446744073709551615)])))) ((.seq ((.assign 1 ((.const 1)))) ((.seq ((.inst ((.arith ((.addCarry 10 10 16 1)))))) ((.seq ((.inst ((.arith ((.addCarry 12 12 14 1)))))) ((.call none ((some 22)) [0, 2, 4, 6, 8, 10, 12] none))))))))))))))))))))))))))), 0) =>
      true
  | _ => false

private def matches16 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (23, 4, (.seq ((.assign 10 ((.const 0)))) ((.seq ((.assign 11 ((.const 64)))) ((.call none ((some 22)) [0, 11, 6, 10, 10, 4, 2] none))))), 0) =>
      true
  | _ => false

private def matches17 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (29, 3, (.seq ((.assign 1 ((.lookup .bitmapBuffer)))) ((.seq ((.assign 3 ((.lookup .codeBuffer)))) ((.seq ((.set .bitmapBuffer ((.var 2)))) ((.seq ((.set .codeBuffer ((.var 4)))) ((.seq ((.install 3 4 1 2 (live11, .ln))) ((.return 0 [3]))))))))))), 0) =>
      decide (live11 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches18 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (30, 4, (.ite .test 2 ((.imm 1)) ((.seq ((.assign 2 ((.lookup .bitmapBuffer)))) ((.call none ((some 31)) [0, 2, 4, 6] none)))) ((.seq ((.assign 3 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 2 ((.load ((.op .add [(.var 3), (.const 8)])))))) ((.seq ((.assign 2 ((.shift .lsr ((.var 2)) (.const 2))))) ((.seq ((.codeBufferWrite 6 2)) ((.seq ((.assign 6 ((.op .add [(.var 6), (.const 1)])))) ((.seq ((.assign 2 ((.load ((.op .add [(.var 3), (.const 16)])))))) ((.call none ((some 30)) [0, 2, 4, 6] none))))))))))))))), 0) =>
      true
  | _ => false

private def matches19 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (31, 4, (.ite .test 4 ((.imm 1)) ((.call none ((some 29)) [0, 2, 6] none)) ((.seq ((.assign 3 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 4 ((.load ((.op .add [(.var 3), (.const 8)])))))) ((.seq ((.assign 4 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 4 ((.load ((.op .add [(.var 4), (.const 8)])))))) ((.seq ((.dataBufferWrite 2 4)) ((.seq ((.assign 2 ((.op .add [(.var 2), (.const 8)])))) ((.seq ((.assign 4 ((.load ((.op .add [(.var 3), (.const 16)])))))) ((.call none ((some 31)) [0, 2, 4, 6] none))))))))))))))))), 0) =>
      true
  | _ => false

private def matches20 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (33, 3, (.ite .test 4 ((.imm 1)) ((.return 0 [2])) ((.seq ((.set ((.temp 0)) ((.var 2)))) ((.seq ((.set ((.temp 1)) ((.var 4)))) ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 3 ((.const 562949953421315)))) ((.seq ((.assign 5 ((.op .sub [(.lookup .triggerGC), (.var 1)])))) ((.seq ((.assign 7 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 5)])))) ((.seq ((.set ((.temp 2)) ((.var 7)))) ((.call none ((some 34)) [0, 1, 4, 3, 5, 7] none))))))))))))))))), 0) =>
      true
  | _ => false

private def matches21 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (34, 6, (.seq ((.assign 1 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 3 ((.load ((.op .add [(.var 1), (.const 8)])))))) ((.seq ((.assign 5 ((.load ((.op .add [(.var 1), (.const 16)])))))) ((.seq ((.ite .lower 8 ((.imm 24)) ((.seq ((.assign 1 ((.const 0)))) ((.call none ((some 35)) [0, 4, 1] none)))) .skip)) ((.seq ((.store ((.var 2)) 6)) ((.seq ((.store ((.op .add [(.var 2), (.const 8)])) 3)) ((.seq ((.ite .test 5 ((.imm 1)) .skip ((.seq ((.assign 10 ((.op .add [(.var 10), (.const 768)])))) ((.seq ((.assign 8 ((.op .sub [(.var 8), (.const 24)])))) ((.seq ((.store ((.op .add [(.var 2), (.const 16)])) 10)) ((.seq ((.assign 2 ((.op .add [(.var 2), (.const 24)])))) ((.call none ((some 34)) [0, 2, 5, 6, 8, 10] none)))))))))))) ((.seq ((.assign 1 ((.lookup ((.temp 0)))))) ((.seq ((.assign 3 ((.lookup ((.temp 2)))))) ((.seq ((.store ((.op .add [(.var 2), (.const 16)])) 1)) ((.seq ((.set .nextFree ((.op .add [(.var 2), (.const 24)])))) ((.return 0 [3]))))))))))))))))))))))), 0) =>
      true
  | _ => false

private def matches22 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (35, 3, (.ite .test 2 ((.imm 1)) ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.seq ((.assign 1 ((.op .add [(.var 4), (.shift .lsr ((.var 1)) (.const 1))])))) ((.seq ((.assign 4 ((.lookup ((.temp 0)))))) ((.seq ((.assign 2 ((.lookup ((.temp 1)))))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 2305843009213693951)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live12, live13))) .skip)))) .skip)))))))) ((.call none ((some 33)) [0, 4, 2] none)))))))))))) ((.seq ((.assign 2 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.const 16)])))))) ((.seq ((.assign 4 ((.op .add [(.var 4), (.const 12)])))) ((.call none ((some 35)) [0, 2, 4] none))))))), 0) =>
      decide (live12 = Flapjack.sptListInsert [0] .ln) &&
      decide (live13 = Flapjack.sptListInsert [2, 4] .ln)
  | _ => false

private def matches23 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (36, 4, (.ite .lower 6 ((.imm 2)) ((.ite .equal 6 ((.imm 0)) ((.seq ((.assign 1 (.const 2))) ((.return 0 [1])))) ((.seq ((.assign 5 ((.load ((.var 4)))))) ((.seq ((.assign 3 ((.load ((.var 2)))))) ((.seq ((.assign 7 ((.op .xor [(.var 5), (.var 3)])))) ((.seq ((.store ((.var 2)) 7)) ((.seq ((.assign 1 (.const 2))) ((.return 0 [1])))))))))))))) ((.seq ((.assign 5 ((.load ((.var 4)))))) ((.seq ((.assign 3 ((.load ((.var 2)))))) ((.seq ((.assign 9 ((.load ((.op .add [(.var 4), (.const 8)])))))) ((.seq ((.assign 7 ((.load ((.op .add [(.var 2), (.const 8)])))))) ((.seq ((.assign 6 ((.op .sub [(.var 6), (.const 2)])))) ((.seq ((.assign 5 ((.op .xor [(.var 5), (.var 3)])))) ((.seq ((.assign 9 ((.op .xor [(.var 9), (.var 7)])))) ((.seq ((.store ((.var 2)) 5)) ((.seq ((.store ((.op .add [(.var 2), (.const 8)])) 9)) ((.seq ((.assign 4 ((.op .add [(.var 4), (.const 16)])))) ((.seq ((.assign 2 ((.op .add [(.var 2), (.const 16)])))) ((.call none ((some 36)) [0, 2, 4, 6] none))))))))))))))))))))))))), 0) =>
      true
  | _ => false

private def matches24 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (37, 6, .skip, 0) =>
      true
  | _ => false

private def matches25 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (38, 6, (.ite .equal 6 ((.imm 8)) ((.return 0 [8, 10])) ((.seq ((.inst ((.mem .load8 1 ((.addr 2 0)))))) ((.seq ((.inst ((.mem .load8 3 ((.addr 4 0)))))) ((.seq ((.ite .notEqual 1 ((.reg 3)) ((.return 0 [1, 3])) .skip)) ((.seq ((.assign 2 ((.op .add [(.var 2), (.const 1)])))) ((.seq ((.assign 4 ((.op .add [(.var 4), (.const 1)])))) ((.seq ((.assign 6 ((.op .sub [(.var 6), (.const 1)])))) ((.call none ((some 38)) [0, 2, 4, 6, 8, 10] none))))))))))))))), 0) =>
      true
  | _ => false

private def matches26 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (24, 5, (.ite .test 2 ((.reg 2)) ((.return 0 [8])) ((.seq ((.assign 1 ((.load ((.var 4)))))) ((.seq ((.assign 2 ((.op .sub [(.var 2), (.const 4)])))) ((.seq ((.assign 4 ((.op .add [(.var 4), (.const 8)])))) ((.seq ((.store ((.var 6)) 1)) ((.seq ((.assign 6 ((.op .add [(.var 6), (.const 8)])))) ((.call none ((some 24)) [0, 2, 4, 6, 8] none))))))))))))), 0) =>
      true
  | _ => false

private def matches27 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (25, 6, (.seq ((.assign 4 ((.shift .lsr ((.var 4)) (.const 2))))) ((.seq ((.assign 6 ((.shift .lsr ((.var 6)) (.const 2))))) ((.seq ((.assign 10 ((.shift .lsr ((.var 10)) (.const 2))))) ((.seq ((.assign 1 (.const 2))) ((.seq ((.assign 2 ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.const 8), (.var 4)])))) ((.seq ((.assign 8 ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 8)) (.const 5))]), (.const 8), (.var 10)])))) ((.ite .lower 4 ((.reg 10)) ((.seq ((.assign 3 ((.op .sub [(.var 6), (.const 1)])))) ((.seq ((.assign 2 ((.op .add [(.var 2), (.var 3)])))) ((.seq ((.assign 8 ((.op .add [(.var 8), (.var 3)])))) ((.call none ((some 27)) [0, 6, 2, 8, 1] none)))))))) ((.call none ((some 26)) [0, 6, 2, 8, 1] none))))))))))))))), 0) =>
      true
  | _ => false

private def matches28 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (26, 5, (.ite .lower 2 ((.imm 4)) ((.ite .lower 2 ((.imm 2)) ((.ite .equal 2 ((.imm 0)) ((.return 0 [8])) ((.seq ((.inst ((.mem .load8 1 ((.addr 4 0)))))) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.return 0 [8])))))))) ((.seq ((.inst ((.mem .load8 1 ((.addr 4 0)))))) ((.seq ((.inst ((.mem .load8 3 ((.addr 4 1)))))) ((.ite .equal 2 ((.imm 2)) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.seq ((.inst ((.mem .store8 3 ((.addr 6 1)))))) ((.return 0 [8])))))) ((.seq ((.inst ((.mem .load8 5 ((.addr 4 2)))))) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.seq ((.inst ((.mem .store8 3 ((.addr 6 1)))))) ((.seq ((.inst ((.mem .store8 5 ((.addr 6 2)))))) ((.return 0 [8])))))))))))))))))) ((.seq ((.inst ((.mem .load8 1 ((.addr 4 0)))))) ((.seq ((.inst ((.mem .load8 3 ((.addr 4 1)))))) ((.seq ((.inst ((.mem .load8 5 ((.addr 4 2)))))) ((.seq ((.inst ((.mem .load8 7 ((.addr 4 3)))))) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.seq ((.inst ((.mem .store8 3 ((.addr 6 1)))))) ((.seq ((.inst ((.mem .store8 5 ((.addr 6 2)))))) ((.seq ((.inst ((.mem .store8 7 ((.addr 6 3)))))) ((.seq ((.assign 9 ((.op .sub [(.var 2), (.const 4)])))) ((.seq ((.assign 11 ((.op .add [(.var 4), (.const 4)])))) ((.seq ((.assign 13 ((.op .add [(.var 6), (.const 4)])))) ((.call none ((some 26)) [0, 9, 11, 13, 8] none))))))))))))))))))))))))), 0) =>
      true
  | _ => false

private def matches29 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (27, 5, (.ite .lower 2 ((.imm 4)) ((.ite .lower 2 ((.imm 2)) ((.ite .equal 2 ((.imm 0)) ((.return 0 [8])) ((.seq ((.inst ((.mem .load8 1 ((.addr 4 0)))))) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.return 0 [8])))))))) ((.seq ((.inst ((.mem .load8 1 ((.addr 4 0)))))) ((.seq ((.inst ((.mem .load8 3 ((.addr 4 18446744073709551615)))))) ((.ite .equal 2 ((.imm 2)) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.seq ((.inst ((.mem .store8 3 ((.addr 6 18446744073709551615)))))) ((.return 0 [8])))))) ((.seq ((.inst ((.mem .load8 5 ((.addr 4 18446744073709551614)))))) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.seq ((.inst ((.mem .store8 3 ((.addr 6 18446744073709551615)))))) ((.seq ((.inst ((.mem .store8 5 ((.addr 6 18446744073709551614)))))) ((.return 0 [8])))))))))))))))))) ((.seq ((.inst ((.mem .load8 1 ((.addr 4 0)))))) ((.seq ((.inst ((.mem .load8 3 ((.addr 4 18446744073709551615)))))) ((.seq ((.inst ((.mem .load8 5 ((.addr 4 18446744073709551614)))))) ((.seq ((.inst ((.mem .load8 7 ((.addr 4 18446744073709551613)))))) ((.seq ((.inst ((.mem .store8 1 ((.addr 6 0)))))) ((.seq ((.inst ((.mem .store8 3 ((.addr 6 18446744073709551615)))))) ((.seq ((.inst ((.mem .store8 5 ((.addr 6 18446744073709551614)))))) ((.seq ((.inst ((.mem .store8 7 ((.addr 6 18446744073709551613)))))) ((.seq ((.assign 9 ((.op .sub [(.var 2), (.const 4)])))) ((.seq ((.assign 11 ((.op .sub [(.var 4), (.const 4)])))) ((.seq ((.assign 13 ((.op .sub [(.var 6), (.const 4)])))) ((.call none ((some 27)) [0, 9, 11, 13, 8] none))))))))))))))))))))))))), 0) =>
      true
  | _ => false

private def matches30 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (28, 4, .skip, 0) =>
      true
  | _ => false

private def matches31 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (32, 0, .skip, 0) =>
      true
  | _ => false

private def matches32 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (39, 1, (.seq ((.seq ((.assign 242 ((.lookup ((.temp 3)))))) fragment29)) ((.return 0 [0]))), 0) =>
      matches_fragment29 fragment29
  | _ => false

private def matches33 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (61, 1, (.seq ((.seq ((.assign 15 ((.lookup ((.temp 1)))))) ((.ite .equal 15 ((.imm 1)) ((.seq ((.seq ((.assign 1 ((.const 0)))) ((.set ((.temp 1)) ((.var 1)))))) .skip)) ((.seq ((.seq ((.assign 2 ((.op .sub [(.lookup ((.temp 1))), (.const 1)])))) ((.set ((.temp 1)) ((.var 2)))))) fragment30)))))) ((.return 0 [0]))), 0) =>
      matches_fragment30 fragment30
  | _ => false

private def matches34 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (60, 1, (.seq ((.seq ((.assign 16 ((.lookup ((.temp 10)))))) ((.seq ((.assign 17 ((.lookup ((.temp 11)))))) fragment31)))) ((.return 0 [0]))), 0) =>
      matches_fragment31 fragment31
  | _ => false

private def matches35 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (59, 1, (.seq ((.seq ((.assign 8 ((.lookup ((.temp 8)))))) ((.ite .equal 8 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 1 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 2 ((.load ((.var 1)))))) ((.set ((.temp 0)) ((.var 2)))))))) ((.seq ((.seq ((.assign 3 ((.op .sub [(.lookup ((.temp 8))), (.const 1)])))) ((.set ((.temp 8)) ((.var 3)))))) ((.seq ((.seq ((.assign 4 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 4)))))) ((.seq ((.seq ((.assign 5 ((.lookup ((.temp 0)))))) ((.seq ((.assign 6 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 11)))) (.const 3))])))) ((.store ((.var 6)) 5)))))) ((.seq ((.seq ((.assign 7 ((.op .add [(.lookup ((.temp 11))), (.const 1)])))) ((.set ((.temp 11)) ((.var 7)))))) ((.seq .skip ((.call none ((some 59)) [0] none)))))))))))))))))) ((.return 0 [0]))), 0) =>
      true
  | _ => false

private def matches36 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (58, 1, (.seq ((.seq ((.assign 11 ((.lookup ((.temp 10)))))) fragment32)) ((.return 0 [0]))), 0) =>
      matches_fragment32 fragment32
  | _ => false

private def matches37 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (54, 1, (.seq ((.seq ((.assign 64 ((.lookup ((.temp 10)))))) ((.ite .equal 64 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 1 ((.lookup ((.temp 14)))))) ((.set ((.temp 6)) ((.var 1)))))) ((.seq ((.seq ((.assign 2 ((.lookup ((.temp 15)))))) ((.set ((.temp 3)) ((.var 2)))))) ((.seq ((.seq ((.assign 3 ((.lookup ((.temp 7)))))) ((.set ((.temp 14)) ((.var 3)))))) ((.seq ((.seq ((.assign 4 ((.lookup ((.temp 9)))))) ((.set ((.temp 15)) ((.var 4)))))) ((.seq ((.seq ((.assign 5 ((.lookup ((.temp 10)))))) ((.set ((.temp 16)) ((.var 5)))))) ((.seq ((.seq ((.assign 6 ((.op .add [(.lookup ((.temp 10))), (.lookup ((.temp 9)))])))) ((.set ((.temp 10)) ((.var 6)))))) ((.seq ((.seq ((.assign 7 ((.op .sub [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 7)))))) ((.seq ((.seq ((.assign 8 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 9 ((.load ((.var 8)))))) ((.set ((.temp 0)) ((.var 9)))))))) fragment37)))))))))))))))))))) ((.return 0 [0]))), 0) =>
      matches_fragment37 fragment37
  | _ => false

private def matches38 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (57, 1, (.seq ((.seq ((.assign 64 ((.lookup ((.temp 9)))))) ((.seq ((.assign 65 ((.lookup ((.temp 11)))))) fragment41)))) ((.return 0 [0]))), 0) =>
      matches_fragment41 fragment41
  | _ => false

private def matches39 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (56, 1, (.seq ((.seq ((.assign 58 ((.lookup ((.temp 9)))))) ((.seq ((.assign 59 ((.lookup ((.temp 11)))))) fragment45)))) ((.return 0 [0]))), 0) =>
      matches_fragment45 fragment45
  | _ => false

private def matches40 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (55, 1, (.seq ((.seq ((.seq ((.seq ((.seq ((.assign 1 ((.lookup ((.temp 6)))))) ((.set ((.temp 0)) ((.var 1)))))) ((.seq ((.seq ((.assign 2 ((.const 0)))) ((.set ((.temp 1)) ((.var 2)))))) ((.seq ((.seq ((.assign 3 ((.lookup ((.temp 7)))))) ((.set ((.temp 2)) ((.var 3)))))) fragment47)))))) ((.seq ((.seq ((.seq ((.assign 39 ((.const 1)))) ((.set ((.temp 0)) ((.var 39)))))) ((.seq ((.assign 54 ((.lookup ((.temp 3)))))) ((.seq ((.assign 55 ((.lookup ((.temp 11)))))) fragment48)))))) ((.seq .skip .skip)))))) fragment51)) ((.return 0 [0]))), 0) =>
      matches_fragment47 fragment47 &&
      matches_fragment48 fragment48 &&
      matches_fragment51 fragment51
  | _ => false

private def matches41 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (53, 1, (.seq ((.seq ((.assign 22 ((.lookup ((.temp 9)))))) ((.seq ((.assign 23 ((.lookup ((.temp 11)))))) ((.ite .equal 22 ((.reg 23)) ((.seq ((.seq ((.assign 1 ((.lookup ((.temp 3)))))) ((.set ((.temp 1)) ((.var 1)))))) ((.seq .skip .skip)))) ((.seq ((.seq ((.assign 2 ((.lookup ((.temp 0)))))) ((.set ((.temp 3)) ((.var 2)))))) ((.seq ((.seq ((.assign 3 ((.op .add [(.lookup ((.temp 30))), (.shift .lsl ((.lookup ((.temp 11)))) (.const 3))])))) ((.seq ((.assign 4 ((.load ((.var 3)))))) ((.set ((.temp 2)) ((.var 4)))))))) ((.seq ((.seq ((.assign 5 ((.lookup ((.temp 8)))))) ((.set ((.temp 0)) ((.var 5)))))) fragment52)))))))))))) ((.return 0 [0]))), 0) =>
      matches_fragment52 fragment52
  | _ => false

private def matches42 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (52, 1, (.seq ((.seq ((.assign 37 ((.lookup ((.temp 9)))))) ((.seq ((.assign 38 ((.lookup ((.temp 11)))))) fragment54)))) ((.return 0 [0]))), 0) =>
      matches_fragment54 fragment54
  | _ => false

private def matches43 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (51, 1, (.seq ((.seq ((.assign 3 ((.lookup ((.temp 1)))))) ((.ite .less 3 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 1 ((.op .add [(.lookup ((.temp 1))), (.lookup ((.temp 1)))])))) ((.set ((.temp 1)) ((.var 1)))))) ((.seq ((.seq ((.assign 2 ((.op .add [(.lookup ((.temp 2))), (.lookup ((.temp 2)))])))) ((.set ((.temp 2)) ((.var 2)))))) ((.call none ((some 51)) [0] none)))))))))) ((.return 0 [0]))), 0) =>
      true
  | _ => false

private def matches44 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (50, 1, (.seq ((.seq ((.assign 11 ((.lookup ((.temp 10)))))) fragment55)) ((.return 0 [0]))), 0) =>
      matches_fragment55 fragment55
  | _ => false

private def matches45 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (49, 1, (.seq ((.seq ((.assign 6 ((.lookup ((.temp 10)))))) ((.ite .equal 6 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 1)))))) ((.seq ((.seq ((.assign 2 ((.op .add [(.lookup ((.temp 31))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 3 ((.load ((.var 2)))))) ((.set ((.temp 0)) ((.var 3)))))))) ((.seq ((.seq ((.assign 4 ((.lookup ((.temp 0)))))) ((.seq ((.assign 5 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 5)) 4)))))) ((.seq .skip ((.call none ((some 49)) [0] none)))))))))))))) ((.return 0 [0]))), 0) =>
      true
  | _ => false

private def matches46 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (47, 1, (.seq ((.seq ((.assign 10 ((.lookup ((.temp 7)))))) fragment56)) ((.return 0 [0]))), 0) =>
      matches_fragment56 fragment56
  | _ => false

private def matches47 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (48, 1, (.seq ((.seq ((.assign 38 ((.lookup ((.temp 9)))))) ((.seq ((.assign 39 ((.lookup ((.temp 11)))))) ((.ite .equal 38 ((.reg 39)) ((.seq ((.seq ((.assign 1 ((.lookup ((.temp 1)))))) ((.seq ((.assign 2 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 2)) 1)))))) ((.seq ((.seq ((.assign 3 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 3)))))) ((.seq .skip .skip)))))) ((.seq ((.seq ((.assign 4 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 5 ((.load ((.var 4)))))) ((.set ((.temp 3)) ((.var 5)))))))) fragment58)))))))) ((.return 0 [0]))), 0) =>
      matches_fragment58 fragment58
  | _ => false

private def matches48 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (46, 1, (.seq ((.seq ((.assign 4 ((.lookup ((.temp 10)))))) ((.ite .equal 4 ((.imm 0)) ((.seq .skip .skip)) ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 1)))))) ((.seq ((.seq ((.assign 2 ((.lookup ((.temp 0)))))) ((.seq ((.assign 3 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.store ((.var 3)) 2)))))) ((.call none ((some 46)) [0] none)))))))))) ((.return 0 [0]))), 0) =>
      true
  | _ => false

private def matches49 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (45, 1, (.seq ((.seq ((.assign 6 ((.lookup ((.temp 10)))))) ((.ite .equal 6 ((.imm 0)) .skip ((.seq ((.seq ((.assign 1 ((.op .sub [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 1)))))) ((.seq ((.seq ((.assign 2 ((.op .add [(.lookup ((.temp 29))), (.shift .lsl ((.lookup ((.temp 10)))) (.const 3))])))) ((.seq ((.assign 3 ((.load ((.var 2)))))) ((.set ((.temp 8)) ((.var 3)))))))) ((.seq ((.assign 5 ((.lookup ((.temp 8)))))) ((.ite .equal 5 ((.imm 0)) ((.call none ((some 45)) [0] none)) ((.seq ((.seq ((.assign 4 ((.op .add [(.lookup ((.temp 10))), (.const 1)])))) ((.set ((.temp 10)) ((.var 4)))))) .skip)))))))))))))) ((.return 0 [0]))), 0) =>
      true
  | _ => false

private def matches50 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (44, 1, (.seq ((.seq ((.assign 13 ((.lookup ((.temp 1)))))) fragment59)) ((.return 0 [0]))), 0) =>
      matches_fragment59 fragment59
  | _ => false

private def matches51 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (43, 1, (.seq ((.seq ((.assign 15 ((.lookup ((.temp 1)))))) ((.ite .equal 15 ((.imm 1)) ((.seq ((.seq ((.assign 1 ((.const 0)))) ((.set ((.temp 1)) ((.var 1)))))) .skip)) ((.seq ((.seq ((.assign 2 ((.op .sub [(.lookup ((.temp 1))), (.const 1)])))) ((.set ((.temp 1)) ((.var 2)))))) fragment60)))))) ((.return 0 [0]))), 0) =>
      matches_fragment60 fragment60
  | _ => false

private def matches52 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (42, 1, (.seq ((.seq ((.assign 12 ((.lookup ((.temp 10)))))) fragment61)) ((.return 0 [0]))), 0) =>
      matches_fragment61 fragment61
  | _ => false

private def matches53 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (41, 1, (.seq ((.seq ((.assign 13 ((.lookup ((.temp 1)))))) fragment62)) ((.return 0 [0]))), 0) =>
      matches_fragment62 fragment62
  | _ => false

private def matches54 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (40, 1, (.seq ((.seq ((.assign 15 ((.lookup ((.temp 1)))))) ((.ite .equal 15 ((.imm 1)) ((.seq ((.seq ((.assign 1 ((.const 0)))) ((.set ((.temp 1)) ((.var 1)))))) .skip)) ((.seq ((.seq ((.assign 2 ((.op .sub [(.lookup ((.temp 1))), (.const 1)])))) ((.set ((.temp 1)) ((.var 2)))))) fragment63)))))) ((.return 0 [0]))), 0) =>
      matches_fragment63 fragment63
  | _ => false

private def matches55 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (62, 2, (.seq ((.assign 4 ((.lookup .globals)))) ((.seq ((.assign 6 ((.const 0)))) ((.seq ((.assign 8 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 6)) (.const 1))])])))))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 2 8 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 2), (.var 8)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live44, live45), .skip, 62, 2))) ((some 13)) [2, 8] none)))))) ((.move 2 [(10, 1)])))))))) ((.seq ((.assign 12 ((.shift .lsl ((.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) (.const 48))) (.const 2))))) fragment65))))))))), 0) =>
      decide (live44 = Flapjack.sptListInsert [0] .ln) &&
      decide (live45 = Flapjack.sptListInsert [4] .ln) &&
      matches_fragment65 fragment65
  | _ => false

private def matches56 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (63, 4, (.seq ((.assign 8 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 6)) (.const 1))])])))))) fragment66), 0) =>
      matches_fragment66 fragment66
  | _ => false

private def matches57 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (64, 1, (.seq ((.assign 2 ((.const 0)))) ((.seq ((.assign 4 ((.const 12)))) fragment67))), 0) =>
      matches_fragment67 fragment67
  | _ => false

private def matches58 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (65, 3, (.seq ((.ite .equal 2 ((.imm 2)) ((.assign 6 (.const 18))) ((.assign 6 (.const 2))))) ((.ite .equal 6 ((.imm 18)) ((.return 0 [4])) ((.seq ((.assign 10 ((.const 4)))) ((.seq ((.assign 12 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 10)) (.const 1))])])))))) ((.seq ((.assign 14 ((.const 4)))) ((.seq ((.seq ((.inst ((.arith ((.addOverflow 1 14 4 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 14), (.var 4)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live66, live67), .skip, 65, 2))) ((some 13)) [14, 4] none)))))) ((.move 2 [(16, 1)])))))))) ((.call none ((some 65)) [0, 12, 16] none))))))))))))), 0) =>
      decide (live66 = Flapjack.sptListInsert [0] .ln) &&
      decide (live67 = Flapjack.sptListInsert [12] .ln)
  | _ => false

private def matches59 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (66, 4, (.seq ((.ite .equal 2 ((.imm 2)) ((.assign 8 (.const 18))) ((.assign 8 (.const 2))))) ((.ite .equal 8 ((.imm 18)) ((.return 0 [6])) ((.seq ((.assign 12 ((.const 0)))) fragment68))))), 0) =>
      matches_fragment68 fragment68
  | _ => false

private def matches60 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (67, 4, (.seq ((.ite .equal 4 ((.imm 0)) ((.assign 8 (.const 18))) ((.assign 8 (.const 2))))) ((.ite .equal 8 ((.imm 18)) ((.return 0 [2])) ((.seq ((.assign 12 ((.const 4)))) ((.seq ((.seq ((.inst ((.arith ((.subOverflow 1 4 12 3)))))) ((.seq ((.assign 3 ((.op .or [(.var 3), (.var 4), (.var 12)])))) ((.seq ((.ite .test 3 ((.imm 1)) .skip ((.mustTerminate ((.call ((some ([1], (live70, live71), .skip, 67, 2))) ((some 14)) [4, 12] none)))))) ((.move 2 [(14, 1)])))))))) fragment69))))))), 0) =>
      decide (live70 = Flapjack.sptListInsert [0] .ln) &&
      decide (live71 = Flapjack.sptListInsert [2, 6] .ln) &&
      matches_fragment69 fragment69
  | _ => false

private def matches61 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (68, 3, (.seq ((.ite .equal 2 ((.imm 2)) ((.assign 6 (.const 18))) ((.assign 6 (.const 2))))) fragment70), 0) =>
      matches_fragment70 fragment70
  | _ => false

private def matches62 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (69, 4, (.seq ((.ite .equal 2 ((.imm 2)) ((.assign 8 (.const 18))) ((.assign 8 (.const 2))))) ((.ite .equal 8 ((.imm 18)) ((.return 0 [6])) ((.seq ((.assign 12 ((.const 0)))) fragment71))))), 0) =>
      matches_fragment71 fragment71
  | _ => false

private def matches63 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (72, 3, (.seq ((.assign 6 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 16)])))))) fragment72), 0) =>
      matches_fragment72 fragment72
  | _ => false

private def matches64 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (76, 1, (.seq ((.assign 2 ((.const 4)))) ((.seq ((.call ((some ([4], (live84, .ln), .skip, 76, 2))) ((some 62)) [2] none)) ((.seq ((.assign 6 (.const 2))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 16)])) 6)) ((.assign 8 (.const 2))))) ((.call none ((some 80)) [0] none))))))))), 0) =>
      decide (live84 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches65 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (80, 1, (.seq ((.assign 2 ((.const 4)))) ((.seq ((.call ((some ([4], (live85, .ln), .skip, 80, 2))) ((some 62)) [2] none)) ((.seq ((.assign 6 (.const 2))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 24)])) 6)) ((.assign 8 (.const 2))))) ((.call none ((some 84)) [0] none))))))))), 0) =>
      decide (live85 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches66 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (84, 1, (.seq ((.call ((some ([2], (live86, .ln), .skip, 84, 2))) ((some 73)) [] none)) ((.seq ((.assign 4 (.const 2))) ((.call none ((some 88)) [0] none))))), 0) =>
      decide (live86 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches67 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (73, 1, (.return 0 [2]), 0) =>
      true
  | _ => false

private def matches68 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (88, 1, (.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 16)) ((.seq .skip ((.seq ((.assign 1 ((.const 16)))) ((.seq ((.alloc 1 (live87, .ln))) .skip)))))) .skip)))) ((.seq ((.assign 2 (.const 2))) ((.seq ((.seq ((.set .triggerGC ((.op .sub [(.lookup .triggerGC), (.const 16)])))) ((.seq ((.assign 1 ((.op .sub [(.lookup .endOfHeap), (.const 16)])))) ((.seq ((.set .endOfHeap ((.var 1)))) ((.seq ((.assign 3 ((.const 281474976710667)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 2)) .skip)))) ((.assign 4 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 1)])))))))))))))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 32)])) 4)) ((.assign 6 (.const 2))))) ((.return 0 [6]))))))))), 0) =>
      decide (live87 = Flapjack.sptListInsert [0] .ln)
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  code.length == 69 &&
    (match code[0]? with | some entry => matches0 entry | none => false) &&
    (match code[1]? with | some entry => matches1 entry | none => false) &&
    (match code[2]? with | some entry => matches2 entry | none => false) &&
    (match code[3]? with | some entry => matches3 entry | none => false) &&
    (match code[4]? with | some entry => matches4 entry | none => false) &&
    (match code[5]? with | some entry => matches5 entry | none => false) &&
    (match code[6]? with | some entry => matches6 entry | none => false) &&
    (match code[7]? with | some entry => matches7 entry | none => false) &&
    (match code[8]? with | some entry => matches8 entry | none => false) &&
    (match code[9]? with | some entry => matches9 entry | none => false) &&
    (match code[10]? with | some entry => matches10 entry | none => false) &&
    (match code[11]? with | some entry => matches11 entry | none => false) &&
    (match code[12]? with | some entry => matches12 entry | none => false) &&
    (match code[13]? with | some entry => matches13 entry | none => false) &&
    (match code[14]? with | some entry => matches14 entry | none => false) &&
    (match code[15]? with | some entry => matches15 entry | none => false) &&
    (match code[16]? with | some entry => matches16 entry | none => false) &&
    (match code[17]? with | some entry => matches17 entry | none => false) &&
    (match code[18]? with | some entry => matches18 entry | none => false) &&
    (match code[19]? with | some entry => matches19 entry | none => false) &&
    (match code[20]? with | some entry => matches20 entry | none => false) &&
    (match code[21]? with | some entry => matches21 entry | none => false) &&
    (match code[22]? with | some entry => matches22 entry | none => false) &&
    (match code[23]? with | some entry => matches23 entry | none => false) &&
    (match code[24]? with | some entry => matches24 entry | none => false) &&
    (match code[25]? with | some entry => matches25 entry | none => false) &&
    (match code[26]? with | some entry => matches26 entry | none => false) &&
    (match code[27]? with | some entry => matches27 entry | none => false) &&
    (match code[28]? with | some entry => matches28 entry | none => false) &&
    (match code[29]? with | some entry => matches29 entry | none => false) &&
    (match code[30]? with | some entry => matches30 entry | none => false) &&
    (match code[31]? with | some entry => matches31 entry | none => false) &&
    (match code[32]? with | some entry => matches32 entry | none => false) &&
    (match code[33]? with | some entry => matches33 entry | none => false) &&
    (match code[34]? with | some entry => matches34 entry | none => false) &&
    (match code[35]? with | some entry => matches35 entry | none => false) &&
    (match code[36]? with | some entry => matches36 entry | none => false) &&
    (match code[37]? with | some entry => matches37 entry | none => false) &&
    (match code[38]? with | some entry => matches38 entry | none => false) &&
    (match code[39]? with | some entry => matches39 entry | none => false) &&
    (match code[40]? with | some entry => matches40 entry | none => false) &&
    (match code[41]? with | some entry => matches41 entry | none => false) &&
    (match code[42]? with | some entry => matches42 entry | none => false) &&
    (match code[43]? with | some entry => matches43 entry | none => false) &&
    (match code[44]? with | some entry => matches44 entry | none => false) &&
    (match code[45]? with | some entry => matches45 entry | none => false) &&
    (match code[46]? with | some entry => matches46 entry | none => false) &&
    (match code[47]? with | some entry => matches47 entry | none => false) &&
    (match code[48]? with | some entry => matches48 entry | none => false) &&
    (match code[49]? with | some entry => matches49 entry | none => false) &&
    (match code[50]? with | some entry => matches50 entry | none => false) &&
    (match code[51]? with | some entry => matches51 entry | none => false) &&
    (match code[52]? with | some entry => matches52 entry | none => false) &&
    (match code[53]? with | some entry => matches53 entry | none => false) &&
    (match code[54]? with | some entry => matches54 entry | none => false) &&
    (match code[55]? with | some entry => matches55 entry | none => false) &&
    (match code[56]? with | some entry => matches56 entry | none => false) &&
    (match code[57]? with | some entry => matches57 entry | none => false) &&
    (match code[58]? with | some entry => matches58 entry | none => false) &&
    (match code[59]? with | some entry => matches59 entry | none => false) &&
    (match code[60]? with | some entry => matches60 entry | none => false) &&
    (match code[61]? with | some entry => matches61 entry | none => false) &&
    (match code[62]? with | some entry => matches62 entry | none => false) &&
    (match code[63]? with | some entry => matches63 entry | none => false) &&
    (match code[64]? with | some entry => matches64 entry | none => false) &&
    (match code[65]? with | some entry => matches65 entry | none => false) &&
    (match code[66]? with | some entry => matches66 entry | none => false) &&
    (match code[67]? with | some entry => matches67 entry | none => false) &&
    (match code[68]? with | some entry => matches68 entry | none => false)

end Flapjack.Test.FullCakeWordOracle
