-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang
import Flapjack.Test.CakeWordOracleHelpers

namespace Flapjack.Test.FixedStubsWordOracle

open Flapjack.Test.CakeWordOracleHelpers

private def matches2 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (9, 4, (.seq ((.ite .test 2 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live3, .ln))))))) ((.seq ((.assign 1 ((.shift .lsr ((.op .add [(.shift .lsr ((.var 2)) (.const 2)), (.const 8)])) (.const 1))))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live4, live5))) .skip)))) .skip)))))))) ((.seq ((.assign 5 ((.shift .lsr ((.op .add [(.shift .lsr ((.var 2)) (.const 2)), (.const 8)])) (.const 3))))) ((.seq ((.assign 7 ((.shift .lsl ((.var 5)) (.const 2))))) ((.seq ((.assign 9 ((.lookup .nextFree)))) ((.seq ((.assign 1 ((.op .add [(.var 9), (.shift .lsl ((.var 5)) (.const 3))])))) ((.seq ((.set .nextFree ((.op .add [(.var 1), (.const 8)])))) ((.seq ((.assign 3 ((.op .or [(.shift .lsl ((.op .sub [(.var 9), (.lookup .currHeap)])) (.const 5)), (.const 1)])))) ((.seq ((.assign 5 ((.op .or [(.op .or [(.shift .lsl ((.op .add [(.shift .lsr ((.var 2)) (.const 2)), (.const 8)])) (.const 45)), (.const 7)]), (.var 6)])))) ((.seq ((.seq ((.assign 4 ((.shift .lsr ((.var 4)) (.const 2))))) ((.seq ((.assign 4 ((.op .or [(.var 4), (.shift .lsl ((.var 4)) (.const 8))])))) ((.seq ((.assign 4 ((.op .or [(.var 4), (.shift .lsl ((.var 4)) (.const 16))])))) ((.assign 4 ((.op .or [(.var 4), (.shift .lsl ((.var 4)) (.const 32))])))))))))) ((.seq ((.store ((.var 9)) 5)) ((.seq ((.assign 11 ((.op .and [(.shift .lsr ((.var 2)) (.const 2)), (.const 7)])))) ((.seq ((.assign 13 ((.const 0)))) ((.seq ((.store ((.var 1)) 13)) ((.seq ((.ite .equal 11 ((.imm 0)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 0)))))) ((.ite .equal 11 ((.imm 1)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 1)))))) ((.ite .equal 11 ((.imm 2)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 2)))))) ((.ite .equal 11 ((.imm 3)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 3)))))) ((.ite .equal 11 ((.imm 4)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 4)))))) ((.ite .equal 11 ((.imm 5)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 5)))))) ((.ite .equal 11 ((.imm 6)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 6)))))) ((.ite .equal 11 ((.imm 7)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 7)))))) .skip)))))))))))))))))))))))))))))))) ((.seq ((.assign 7 ((.op .sub [(.var 7), (.const 4)])))) ((.call none ((some 11)) [0, 9, 4, 7, 3] none))))))))))))))))))))))))))))))))))), 0) =>
      decide (live3 = Flapjack.sptListInsert [0] .ln) &&
      decide (live4 = Flapjack.sptListInsert [0] .ln) &&
      decide (live5 = Flapjack.sptListInsert [2, 4, 6] .ln)
  | _ => false

private def matches5 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (12, 4, (.seq ((.assign 1 ((.const 4)))) ((.seq ((.ite .equal 2 ((.imm 0)) .skip ((.ite .test 2 ((.imm 1)) ((.assign 1 ((.op .add [(.var 1), (.const 4)])))) ((.assign 1 ((.op .add [(.var 1), (.shift .lsl ((.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) (.const 48))) (.const 2))])))))))) ((.seq ((.ite .equal 4 ((.imm 0)) .skip ((.ite .test 4 ((.imm 1)) ((.assign 1 ((.op .add [(.var 1), (.const 4)])))) ((.assign 1 ((.op .add [(.var 1), (.shift .lsl ((.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) (.const 48))) (.const 2))])))))))) ((.seq ((.set ((.temp 29)) ((.var 1)))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live6, live7))) .skip)))) .skip)))))))) ((.seq ((.ite .equal 2 ((.imm 0)) ((.seq ((.assign 7 ((.const 0)))) ((.seq ((.set ((.temp 0)) ((.var 2)))) ((.seq ((.set ((.temp 31)) ((.var 2)))) ((.set ((.temp 12)) ((.var 2)))))))))) ((.ite .notTest 2 ((.imm 1)) ((.seq ((.assign 7 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.set ((.temp 31)) ((.op .add [(.var 7), (.const 8)])))) ((.seq ((.set ((.temp 0)) ((.op .add [(.shift .lsl ((.shift .lsr ((.load ((.var 7)))) (.const 48))) (.const 1)), (.op .and [(.const 1), (.shift .lsr ((.load ((.var 7)))) (.const 4))])])))) ((.set ((.temp 12)) ((.const 0)))))))))) ((.ite .notLess 2 ((.imm 0)) ((.seq ((.set ((.temp 0)) (.const 2))) ((.seq ((.set ((.temp 31)) ((.lookup .nextFree)))) ((.seq ((.set ((.temp 12)) ((.shift .lsr ((.var 2)) (.const 2))))) ((.assign 7 ((.const 0)))))))))) ((.seq ((.set ((.temp 0)) ((.const 3)))) ((.seq ((.set ((.temp 31)) ((.lookup .nextFree)))) ((.seq ((.set ((.temp 12)) ((.op .sub [(.const 0), (.shift .asr ((.var 2)) (.const 2))])))) ((.assign 7 ((.const 0)))))))))))))))) ((.seq ((.ite .equal 4 ((.imm 0)) ((.seq ((.assign 7 ((.const 0)))) ((.seq ((.set ((.temp 1)) ((.var 4)))) ((.seq ((.set ((.temp 30)) ((.var 4)))) ((.set ((.temp 11)) ((.var 4)))))))))) ((.ite .notTest 4 ((.imm 1)) ((.seq ((.assign 7 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.set ((.temp 30)) ((.op .add [(.var 7), (.const 8)])))) ((.seq ((.set ((.temp 1)) ((.op .add [(.shift .lsl ((.shift .lsr ((.load ((.var 7)))) (.const 48))) (.const 1)), (.op .and [(.const 1), (.shift .lsr ((.load ((.var 7)))) (.const 4))])])))) ((.set ((.temp 11)) ((.const 0)))))))))) ((.ite .notLess 4 ((.imm 0)) ((.seq ((.set ((.temp 1)) (.const 2))) ((.seq ((.set ((.temp 30)) ((.lookup .otherHeap)))) ((.seq ((.set ((.temp 11)) ((.shift .lsr ((.var 4)) (.const 2))))) ((.assign 7 ((.const 0)))))))))) ((.seq ((.set ((.temp 1)) ((.const 3)))) ((.seq ((.set ((.temp 30)) ((.lookup .otherHeap)))) ((.seq ((.set ((.temp 11)) ((.op .sub [(.const 0), (.shift .asr ((.var 4)) (.const 2))])))) ((.assign 7 ((.const 0)))))))))))))))) ((.seq ((.get 1 ((.temp 11)))) ((.seq ((.store ((.lookup .otherHeap)) 1)) ((.seq ((.get 1 ((.temp 12)))) ((.seq ((.store ((.lookup .nextFree)) 1)) ((.seq ((.get 1 ((.temp 29)))) ((.seq ((.assign 2 ((.lookup .nextFree)))) ((.seq ((.set ((.temp 29)) ((.var 2)))) ((.seq ((.set ((.temp 3)) ((.shift .lsr ((.var 6)) (.const 2))))) ((.seq ((.assign 3 ((.const 0)))) ((.seq ((.call ((some ([0], (live8, .ln), .skip, 12, 2))) ((some 11)) [2, 3, 1, 0] none)) ((.seq ((.set ((.temp 29)) ((.op .add [(.lookup ((.temp 29))), (.const 8)])))) ((.seq ((.call ((some ([1], (live9, .ln), .skip, 12, 3))) ((some 39)) [] none)) ((.seq ((.get 1 ((.temp 10)))) ((.seq ((.ite .test 1 ((.reg 1)) ((.return 0 [1])) .skip)) ((.seq ((.assign 3 ((.load ((.op .add [(.lookup .nextFree), (.const 8)])))))) ((.seq ((.ite .equal 1 ((.imm 2)) ((.seq ((.assign 5 ((.shift .lsr ((.var 3)) (.const 61))))) ((.ite .test 5 ((.reg 5)) ((.seq ((.assign 1 ((.shift .lsl ((.var 3)) (.const 2))))) ((.return 0 [1])))) .skip)))) ((.ite .equal 1 ((.imm 3)) ((.seq ((.assign 5 ((.shift .lsr ((.op .sub [(.var 3), (.const 1)])) (.const 61))))) ((.ite .test 5 ((.reg 5)) ((.seq ((.assign 1 ((.op .sub [(.const 0), (.shift .lsl ((.var 3)) (.const 2))])))) ((.return 0 [1])))) .skip)))) ((.assign 5 ((.const 0)))))))) ((.seq ((.assign 5 ((.lookup .nextFree)))) ((.seq ((.assign 6 ((.shift .lsr ((.var 1)) (.const 1))))) ((.seq ((.assign 8 ((.op .and [(.var 1), (.const 1)])))) ((.seq ((.assign 7 ((.op .or [(.const 15), (.shift .lsl ((.var 6)) (.const 48)), (.shift .lsl ((.var 8)) (.const 4))])))) ((.seq ((.store ((.var 5)) 7)) ((.seq ((.assign 1 ((.op .sub [(.var 5), (.lookup .currHeap)])))) ((.seq ((.assign 1 ((.op .or [(.shift .lsl ((.var 1)) (.const 5)), (.const 1)])))) ((.seq ((.set .nextFree ((.op .add [(.var 5), (.const 8), (.shift .lsl ((.var 6)) (.const 3))])))) ((.return 0 [1]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), 0) =>
      decide (live6 = Flapjack.sptListInsert [0] .ln) &&
      decide (live7 = Flapjack.sptListInsert [2, 4, 6] .ln) &&
      decide (live8 = Flapjack.sptListInsert [0] .ln) &&
      decide (live9 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches12 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (19, 3, (.ite .test 2 ((.imm 1)) ((.seq ((.assign 1 ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))))) ((.ite .test 1 ((.imm 16)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))))))) ((.ite .test 4 ((.imm 1)) ((.seq ((.assign 1 ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))))) ((.ite .test 1 ((.imm 16)) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))))))) ((.seq ((.assign 11 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 1 ((.load ((.var 11)))))) ((.seq ((.assign 13 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 3 ((.load ((.var 13)))))) ((.seq ((.assign 6 ((.shift .lsr ((.var 1)) (.const 48))))) ((.seq ((.assign 8 ((.shift .lsr ((.var 3)) (.const 48))))) ((.ite .equal 1 ((.reg 3)) ((.seq ((.assign 2 ((.op .add [(.var 11), (.shift .lsl ((.var 6)) (.const 3))])))) ((.seq ((.assign 4 ((.op .add [(.var 13), (.shift .lsl ((.var 6)) (.const 3))])))) ((.ite .test 1 ((.imm 16)) ((.call none ((some 18)) [0, 6, 2, 4] none)) ((.call none ((some 18)) [0, 6, 4, 2] none)))))))) ((.ite .test 1 ((.imm 16)) ((.ite .test 3 ((.imm 16)) ((.ite .lower 6 ((.reg 8)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))))) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))))) ((.ite .test 3 ((.imm 16)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) ((.ite .lower 6 ((.reg 8)) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2]))))))))))))))))))))))))))), 0) =>
      true
  | _ => false

private def matches14 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (21, 3, (.seq ((.ite .equal 2 ((.reg 4)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 1 ((.op .and [(.var 2), (.var 4)])))) ((.seq ((.ite .test 1 ((.imm 1)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 20 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 40 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 21 ((.load ((.var 20)))))) ((.seq ((.assign 41 ((.load ((.var 40)))))) ((.seq ((.ite .test 21 ((.imm 12)) ((.seq ((.assign 1 ((.op .and [(.var 21), (.const 281474976710654)])))) ((.seq ((.ite .equal 1 ((.imm 482)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) .skip)) ((.seq ((.ite .equal 1 ((.imm 498)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) .skip)) ((.seq ((.ite .equal 21 ((.reg 41)) .skip ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))))) ((.seq ((.assign 6 ((.shift .lsr ((.var 21)) (.const 48))))) ((.seq ((.assign 20 ((.op .add [(.var 20), (.const 8)])))) ((.seq ((.assign 40 ((.op .add [(.var 40), (.const 8)])))) ((.call none ((some 20)) [0, 6, 20, 40] none)))))))))))))))) .skip)) ((.seq ((.ite .equal 21 ((.reg 41)) .skip ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))))) ((.seq ((.ite .test 21 ((.imm 4)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 1 ((.op .and [(.var 21), (.const 24)])))) ((.seq ((.ite .equal 1 ((.imm 16)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 6 ((.shift .lsr ((.var 21)) (.const 48))))) ((.seq ((.assign 2 ((.op .add [(.var 20), (.shift .lsl ((.var 6)) (.const 3))])))) ((.seq ((.assign 4 ((.op .add [(.var 40), (.shift .lsl ((.var 6)) (.const 3))])))) ((.call none ((some 18)) [0, 6, 2, 4] none))))))))))))))))))))))))))))))), 0) =>
      true
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0, entry1, entry2, entry3, entry4, entry5, entry6, entry7, entry8, entry9, entry10, entry11, entry12, entry13, entry14, entry15, entry16, entry17, entry18, entry19, entry20, entry21, entry22, entry23, entry24, entry25, entry26, entry27, entry28, entry29, entry30, entry31] =>
      shared_matches0_2 entry0 &&
      shared_matches1_2 entry1 &&
      matches2 entry2 &&
      shared_matches3_2 entry3 &&
      shared_matches4_2 entry4 &&
      matches5 entry5 &&
      shared_matches6_2 entry6 &&
      shared_matches7_2 entry7 &&
      shared_matches8_2 entry8 &&
      shared_matches9_2 entry9 &&
      shared_matches10_2 entry10 &&
      shared_matches11_2 entry11 &&
      matches12 entry12 &&
      shared_matches13_2 entry13 &&
      matches14 entry14 &&
      shared_matches15 entry15 &&
      shared_matches16 entry16 &&
      shared_matches17 entry17 &&
      shared_matches18 entry18 &&
      shared_matches19 entry19 &&
      shared_matches20 entry20 &&
      shared_matches21 entry21 &&
      shared_matches22 entry22 &&
      shared_matches23 entry23 &&
      shared_matches24 entry24 &&
      shared_matches25 entry25 &&
      shared_matches26 entry26 &&
      shared_matches27 entry27 &&
      shared_matches28 entry28 &&
      shared_matches29 entry29 &&
      shared_matches30 entry30 &&
      shared_matches31 entry31
  | _ => false

end Flapjack.Test.FixedStubsWordOracle
