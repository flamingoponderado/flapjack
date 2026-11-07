-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.FixedStubsWordOracle

private def matches0 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (7, 4, (.ite .equal 2 ((.imm 0)) ((.seq ((.assign 6 ((.op .add [(.var 6), (.const 2)])))) ((.return 0 [6])))) ((.seq ((.ite .test 2 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live0, .ln))))))) ((.seq ((.assign 1 ((.var 2)))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live1, live2))) .skip)))) .skip)))))))) ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.assign 5 ((.op .or [(.shift .lsl ((.var 2)) (.const 46)), (.const 3), (.var 6)])))) ((.seq ((.assign 7 ((.shift .lsr ((.var 2)) (.const 2))))) ((.seq ((.assign 9 ((.shift .lsr ((.var 6)) (.const 4))))) ((.seq ((.seq ((.assign 3 ((.op .or [(.const 1), (.shift .lsl ((.op .sub [(.lookup .nextFree), (.lookup .currHeap)])) (.const 5))])))) ((.seq ((.ite .lower 9 ((.imm 1)) ((.assign 3 ((.op .or [(.var 3), (.shift .lsl ((.var 9)) (.const 3))])))) ((.assign 3 ((.op .or [(.var 3), (.const 8)])))))) ((.ite .lower 7 ((.imm 3)) ((.assign 3 ((.op .or [(.var 3), (.shift .lsl ((.var 7)) (.const 1))])))) ((.assign 3 ((.op .or [(.var 3), (.const 6)])))))))))) ((.call none ((some 8)) [0, 1, 4, 2, 3, 5] none))))))))))))))))))), 0) =>
      decide (live0 = Flapjack.sptListInsert [0] .ln) &&
      decide (live1 = Flapjack.sptListInsert [0] .ln) &&
      decide (live2 = Flapjack.sptListInsert [2, 4, 6] .ln)
  | _ => false

private def matches1 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (8, 6, (.seq ((.store ((.var 2)) 10)) ((.seq ((.assign 2 ((.op .add [(.var 2), (.const 8)])))) ((.ite .equal 6 ((.imm 0)) ((.seq ((.set .nextFree ((.var 2)))) ((.return 0 [8])))) ((.seq ((.assign 4 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 10 ((.load ((.op .add [(.var 4), (.const 8)])))))) ((.seq ((.assign 4 ((.load ((.op .add [(.var 4), (.const 16)])))))) ((.seq ((.assign 6 ((.op .sub [(.var 6), (.const 4)])))) ((.call none ((some 8)) [0, 2, 4, 6, 8, 10] none))))))))))))))), 0) =>
      true
  | _ => false

private def matches2 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (9, 4, (.seq ((.ite .test 2 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live3, .ln))))))) ((.seq ((.assign 1 ((.shift .lsr ((.op .add [(.shift .lsr ((.var 2)) (.const 2)), (.const 8)])) (.const 1))))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live4, live5))) .skip)))) .skip)))))))) ((.seq ((.assign 5 ((.shift .lsr ((.op .add [(.shift .lsr ((.var 2)) (.const 2)), (.const 8)])) (.const 3))))) ((.seq ((.assign 7 ((.shift .lsl ((.var 5)) (.const 2))))) ((.seq ((.assign 9 ((.lookup .nextFree)))) ((.seq ((.assign 1 ((.op .add [(.var 9), (.shift .lsl ((.var 5)) (.const 3))])))) ((.seq ((.set .nextFree ((.op .add [(.var 1), (.const 8)])))) ((.seq ((.assign 3 ((.op .or [(.shift .lsl ((.op .sub [(.var 9), (.lookup .currHeap)])) (.const 5)), (.const 1)])))) ((.seq ((.assign 5 ((.op .or [(.op .or [(.shift .lsl ((.op .add [(.shift .lsr ((.var 2)) (.const 2)), (.const 8)])) (.const 45)), (.const 7)]), (.var 6)])))) ((.seq ((.seq ((.assign 4 ((.shift .lsr ((.var 4)) (.const 2))))) ((.seq ((.assign 4 ((.op .or [(.var 4), (.shift .lsl ((.var 4)) (.const 8))])))) ((.seq ((.assign 4 ((.op .or [(.var 4), (.shift .lsl ((.var 4)) (.const 16))])))) ((.assign 4 ((.op .or [(.var 4), (.shift .lsl ((.var 4)) (.const 32))])))))))))) ((.seq ((.store ((.var 9)) 5)) ((.seq ((.assign 11 ((.op .and [(.shift .lsr ((.var 2)) (.const 2)), (.const 7)])))) ((.seq ((.assign 13 ((.const 0)))) ((.seq ((.store ((.var 1)) 13)) ((.seq ((.ite .equal 11 ((.imm 0)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 0)))))) ((.ite .equal 11 ((.imm 1)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 1)))))) ((.ite .equal 11 ((.imm 2)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 2)))))) ((.ite .equal 11 ((.imm 3)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 3)))))) ((.ite .equal 11 ((.imm 4)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 4)))))) ((.ite .equal 11 ((.imm 5)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 5)))))) ((.ite .equal 11 ((.imm 6)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 6)))))) ((.ite .equal 11 ((.imm 7)) .skip ((.seq ((.inst ((.mem .store8 4 ((.addr 1 7)))))) .skip)))))))))))))))))))))))))))))))) ((.seq ((.assign 7 ((.op .sub [(.var 7), (.const 4)])))) ((.call none ((some 11)) [0, 9, 4, 7, 3] none))))))))))))))))))))))))))))))))))), 0) =>
      decide (live3 = Flapjack.sptListInsert [0] .ln) &&
      decide (live4 = Flapjack.sptListInsert [0] .ln) &&
      decide (live5 = Flapjack.sptListInsert [2, 4, 6] .ln)
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
  | (12, 4, (.seq ((.assign 1 ((.const 4)))) ((.seq ((.ite .equal 2 ((.imm 0)) .skip ((.ite .test 2 ((.imm 1)) ((.assign 1 ((.op .add [(.var 1), (.const 4)])))) ((.assign 1 ((.op .add [(.var 1), (.shift .lsl ((.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) (.const 48))) (.const 2))])))))))) ((.seq ((.ite .equal 4 ((.imm 0)) .skip ((.ite .test 4 ((.imm 1)) ((.assign 1 ((.op .add [(.var 1), (.const 4)])))) ((.assign 1 ((.op .add [(.var 1), (.shift .lsl ((.shift .lsr ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) (.const 48))) (.const 2))])))))))) ((.seq ((.set ((.temp 29)) ((.var 1)))) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live6, live7))) .skip)))) .skip)))))))) ((.seq ((.ite .equal 2 ((.imm 0)) ((.seq ((.assign 7 ((.const 0)))) ((.seq ((.set ((.temp 0)) ((.var 2)))) ((.seq ((.set ((.temp 31)) ((.var 2)))) ((.set ((.temp 12)) ((.var 2)))))))))) ((.ite .notTest 2 ((.imm 1)) ((.seq ((.assign 7 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.set ((.temp 31)) ((.op .add [(.var 7), (.const 8)])))) ((.seq ((.set ((.temp 0)) ((.op .add [(.shift .lsl ((.shift .lsr ((.load ((.var 7)))) (.const 48))) (.const 1)), (.op .and [(.const 1), (.shift .lsr ((.load ((.var 7)))) (.const 4))])])))) ((.set ((.temp 12)) ((.const 0)))))))))) ((.ite .notLess 2 ((.imm 0)) ((.seq ((.set ((.temp 0)) (.const 2))) ((.seq ((.set ((.temp 31)) ((.lookup .nextFree)))) ((.seq ((.set ((.temp 12)) ((.shift .lsr ((.var 2)) (.const 2))))) ((.assign 7 ((.const 0)))))))))) ((.seq ((.set ((.temp 0)) ((.const 3)))) ((.seq ((.set ((.temp 31)) ((.lookup .nextFree)))) ((.seq ((.set ((.temp 12)) ((.op .sub [(.const 0), (.shift .asr ((.var 2)) (.const 2))])))) ((.assign 7 ((.const 0)))))))))))))))) ((.seq ((.ite .equal 4 ((.imm 0)) ((.seq ((.assign 7 ((.const 0)))) ((.seq ((.set ((.temp 1)) ((.var 4)))) ((.seq ((.set ((.temp 30)) ((.var 4)))) ((.set ((.temp 11)) ((.var 4)))))))))) ((.ite .notTest 4 ((.imm 1)) ((.seq ((.assign 7 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.set ((.temp 30)) ((.op .add [(.var 7), (.const 8)])))) ((.seq ((.set ((.temp 1)) ((.op .add [(.shift .lsl ((.shift .lsr ((.load ((.var 7)))) (.const 48))) (.const 1)), (.op .and [(.const 1), (.shift .lsr ((.load ((.var 7)))) (.const 4))])])))) ((.set ((.temp 11)) ((.const 0)))))))))) ((.ite .notLess 4 ((.imm 0)) ((.seq ((.set ((.temp 1)) (.const 2))) ((.seq ((.set ((.temp 30)) ((.lookup .otherHeap)))) ((.seq ((.set ((.temp 11)) ((.shift .lsr ((.var 4)) (.const 2))))) ((.assign 7 ((.const 0)))))))))) ((.seq ((.set ((.temp 1)) ((.const 3)))) ((.seq ((.set ((.temp 30)) ((.lookup .otherHeap)))) ((.seq ((.set ((.temp 11)) ((.op .sub [(.const 0), (.shift .asr ((.var 4)) (.const 2))])))) ((.assign 7 ((.const 0)))))))))))))))) ((.seq ((.get 1 ((.temp 11)))) ((.seq ((.store ((.lookup .otherHeap)) 1)) ((.seq ((.get 1 ((.temp 12)))) ((.seq ((.store ((.lookup .nextFree)) 1)) ((.seq ((.get 1 ((.temp 29)))) ((.seq ((.assign 2 ((.lookup .nextFree)))) ((.seq ((.set ((.temp 29)) ((.var 2)))) ((.seq ((.set ((.temp 3)) ((.shift .lsr ((.var 6)) (.const 2))))) ((.seq ((.assign 3 ((.const 0)))) ((.seq ((.call ((some ([0], (live8, .ln), .skip, 12, 2))) ((some 11)) [2, 3, 1, 0] none)) ((.seq ((.set ((.temp 29)) ((.op .add [(.lookup ((.temp 29))), (.const 8)])))) ((.seq ((.call ((some ([1], (live9, .ln), .skip, 12, 3))) ((some 39)) [] none)) ((.seq ((.get 1 ((.temp 10)))) ((.seq ((.ite .test 1 ((.reg 1)) ((.return 0 [1])) .skip)) ((.seq ((.assign 3 ((.load ((.op .add [(.lookup .nextFree), (.const 8)])))))) ((.seq ((.ite .equal 1 ((.imm 2)) ((.seq ((.assign 5 ((.shift .lsr ((.var 3)) (.const 61))))) ((.ite .test 5 ((.reg 5)) ((.seq ((.assign 1 ((.shift .lsl ((.var 3)) (.const 2))))) ((.return 0 [1])))) .skip)))) ((.ite .equal 1 ((.imm 3)) ((.seq ((.assign 5 ((.shift .lsr ((.op .sub [(.var 3), (.const 1)])) (.const 61))))) ((.ite .test 5 ((.reg 5)) ((.seq ((.assign 1 ((.op .sub [(.const 0), (.shift .lsl ((.var 3)) (.const 2))])))) ((.return 0 [1])))) .skip)))) ((.assign 5 ((.const 0)))))))) ((.seq ((.assign 5 ((.lookup .nextFree)))) ((.seq ((.assign 6 ((.shift .lsr ((.var 1)) (.const 1))))) ((.seq ((.assign 8 ((.op .and [(.var 1), (.const 1)])))) ((.seq ((.assign 7 ((.op .or [(.const 15), (.shift .lsl ((.var 6)) (.const 48)), (.shift .lsl ((.var 8)) (.const 4))])))) ((.seq ((.store ((.var 5)) 7)) ((.seq ((.assign 1 ((.op .sub [(.var 5), (.lookup .currHeap)])))) ((.seq ((.assign 1 ((.op .or [(.shift .lsl ((.var 1)) (.const 5)), (.const 1)])))) ((.seq ((.set .nextFree ((.op .add [(.var 5), (.const 8), (.shift .lsl ((.var 6)) (.const 3))])))) ((.return 0 [1]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), 0) =>
      decide (live6 = Flapjack.sptListInsert [0] .ln) &&
      decide (live7 = Flapjack.sptListInsert [2, 4, 6] .ln) &&
      decide (live8 = Flapjack.sptListInsert [0] .ln) &&
      decide (live9 = Flapjack.sptListInsert [0] .ln)
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
  | (19, 3, (.ite .test 2 ((.imm 1)) ((.seq ((.assign 1 ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))))) ((.ite .test 1 ((.imm 16)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))))))) ((.ite .test 4 ((.imm 1)) ((.seq ((.assign 1 ((.load ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))))) ((.ite .test 1 ((.imm 16)) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))))))) ((.seq ((.assign 11 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 1 ((.load ((.var 11)))))) ((.seq ((.assign 13 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 3 ((.load ((.var 13)))))) ((.seq ((.assign 6 ((.shift .lsr ((.var 1)) (.const 48))))) ((.seq ((.assign 8 ((.shift .lsr ((.var 3)) (.const 48))))) ((.ite .equal 1 ((.reg 3)) ((.seq ((.assign 2 ((.op .add [(.var 11), (.shift .lsl ((.var 6)) (.const 3))])))) ((.seq ((.assign 4 ((.op .add [(.var 13), (.shift .lsl ((.var 6)) (.const 3))])))) ((.ite .test 1 ((.imm 16)) ((.call none ((some 18)) [0, 6, 2, 4] none)) ((.call none ((some 18)) [0, 6, 4, 2] none)))))))) ((.ite .test 1 ((.imm 16)) ((.ite .test 3 ((.imm 16)) ((.ite .lower 6 ((.reg 8)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))))) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))))) ((.ite .test 3 ((.imm 16)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) ((.ite .lower 6 ((.reg 8)) ((.seq ((.assign 2 (.const 2))) ((.return 0 [2])))) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2]))))))))))))))))))))))))))), 0) =>
      true
  | _ => false

private def matches13 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (20, 4, (.seq ((.ite .equal 2 ((.imm 0)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 1 ((.load ((.var 4)))))) ((.seq ((.assign 3 ((.load ((.var 6)))))) ((.seq ((.call ((some ([5], (live10, .ln), .skip, 20, 2))) ((some 21)) [1, 3] none)) ((.seq ((.ite .equal 5 ((.imm 1)) .skip ((.return 0 [5])))) ((.seq ((.assign 2 ((.op .sub [(.var 2), (.const 1)])))) ((.seq ((.assign 4 ((.op .add [(.var 4), (.const 8)])))) ((.seq ((.assign 6 ((.op .add [(.var 6), (.const 8)])))) ((.call none ((some 20)) [0, 2, 4, 6] none))))))))))))))))), 0) =>
      decide (live10 = Flapjack.sptListInsert [0, 2, 4, 6] .ln)
  | _ => false

private def matches14 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (21, 3, (.seq ((.ite .equal 2 ((.reg 4)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 1 ((.op .and [(.var 2), (.var 4)])))) ((.seq ((.ite .test 1 ((.imm 1)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 20 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 40 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))])))) ((.seq ((.assign 21 ((.load ((.var 20)))))) ((.seq ((.assign 41 ((.load ((.var 40)))))) ((.seq ((.ite .test 21 ((.imm 12)) ((.seq ((.assign 1 ((.op .and [(.var 21), (.const 281474976710654)])))) ((.seq ((.ite .equal 1 ((.imm 482)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) .skip)) ((.seq ((.ite .equal 1 ((.imm 498)) ((.seq ((.assign 2 ((.const 1)))) ((.return 0 [2])))) .skip)) ((.seq ((.ite .equal 21 ((.reg 41)) .skip ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))))) ((.seq ((.assign 6 ((.shift .lsr ((.var 21)) (.const 48))))) ((.seq ((.assign 20 ((.op .add [(.var 20), (.const 8)])))) ((.seq ((.assign 40 ((.op .add [(.var 40), (.const 8)])))) ((.call none ((some 20)) [0, 6, 20, 40] none)))))))))))))))) .skip)) ((.seq ((.ite .equal 21 ((.reg 41)) .skip ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))))) ((.seq ((.ite .test 21 ((.imm 4)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 1 ((.op .and [(.var 21), (.const 24)])))) ((.seq ((.ite .equal 1 ((.imm 16)) ((.seq ((.assign 2 ((.const 0)))) ((.return 0 [2])))) .skip)) ((.seq ((.assign 6 ((.shift .lsr ((.var 21)) (.const 48))))) ((.seq ((.assign 2 ((.op .add [(.var 20), (.shift .lsl ((.var 6)) (.const 3))])))) ((.seq ((.assign 4 ((.op .add [(.var 40), (.shift .lsl ((.var 6)) (.const 3))])))) ((.call none ((some 18)) [0, 6, 2, 4] none))))))))))))))))))))))))))))))), 0) =>
      true
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

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0, entry1, entry2, entry3, entry4, entry5, entry6, entry7, entry8, entry9, entry10, entry11, entry12, entry13, entry14, entry15, entry16, entry17, entry18, entry19, entry20, entry21, entry22, entry23, entry24, entry25, entry26, entry27, entry28, entry29, entry30, entry31] =>
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
      matches14 entry14 &&
      matches15 entry15 &&
      matches16 entry16 &&
      matches17 entry17 &&
      matches18 entry18 &&
      matches19 entry19 &&
      matches20 entry20 &&
      matches21 entry21 &&
      matches22 entry22 &&
      matches23 entry23 &&
      matches24 entry24 &&
      matches25 entry25 &&
      matches26 entry26 &&
      matches27 entry27 &&
      matches28 entry28 &&
      matches29 entry29 &&
      matches30 entry30 &&
      matches31 entry31
  | _ => false

end Flapjack.Test.FixedStubsWordOracle
