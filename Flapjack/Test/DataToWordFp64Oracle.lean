-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.DataToWordFp64Oracle

private def matches0 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (0, 0, (.seq ((.assign 3 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 8)])))))) ((.seq ((.assign 5 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.const 8)])))))) ((.seq ((.inst ((.fp ((.fpMovFromReg 0 3 3)))))) ((.seq ((.inst ((.fp ((.fpMovFromReg 1 5 5)))))) ((.seq ((.inst ((.fp ((.fpLess 3 0 1)))))) ((.assign 8 ((.op .add [(.shift .lsl ((.var 3)) (.const 4)), (.const 2)]))))))))))))), 7) =>
      true
  | _ => false

private def matches1 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (1, 0, (.seq ((.assign 3 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 8)])))))) ((.seq ((.assign 5 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.const 8)])))))) ((.seq ((.inst ((.fp ((.fpMovFromReg 0 3 3)))))) ((.seq ((.inst ((.fp ((.fpMovFromReg 1 5 5)))))) ((.seq ((.inst ((.fp ((.fpLessEqual 3 1 0)))))) ((.assign 8 ((.op .add [(.shift .lsl ((.var 3)) (.const 4)), (.const 2)]))))))))))))), 7) =>
      true
  | _ => false

private def matches2 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (2, 0, (.seq ((.assign 3 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 8)])))))) ((.seq ((.assign 5 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.const 8)])))))) ((.seq ((.inst ((.fp ((.fpMovFromReg 0 3 3)))))) ((.seq ((.inst ((.fp ((.fpMovFromReg 1 5 5)))))) ((.seq ((.inst ((.fp ((.fpSub 0 0 1)))))) ((.seq ((.inst ((.fp ((.fpMovToReg 3 5 0)))))) ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 3)) ((.seq ((.assign 3 ((.const 281474976710671)))) ((.seq ((.store ((.var 1)) 3)) ((.seq ((.set .nextFree ((.op .add [(.var 1), (.const 16)])))) ((.assign 8 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 1)]))))))))))))))))))))))))), 7) =>
      true
  | _ => false

private def matches3 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (3, 0, (.seq ((.assign 3 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 8)])))))) ((.seq ((.inst ((.fp ((.fpMovFromReg 0 3 3)))))) ((.seq ((.inst ((.fp ((.fpSqrt 1 0)))))) ((.seq ((.inst ((.fp ((.fpMovToReg 3 5 1)))))) ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 3)) ((.seq ((.assign 3 ((.const 281474976710671)))) ((.seq ((.store ((.var 1)) 3)) ((.seq ((.set .nextFree ((.op .add [(.var 1), (.const 16)])))) ((.assign 8 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 1)]))))))))))))))))))))), 7) =>
      true
  | _ => false

private def matches4 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (4, 0, (.seq ((.assign 3 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 8)])))))) ((.seq ((.assign 5 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.const 8)])))))) ((.seq ((.assign 7 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 8)) (.const 5))]), (.const 8)])))))) ((.seq ((.inst ((.fp ((.fpMovFromReg 0 3 3)))))) ((.seq ((.inst ((.fp ((.fpMovFromReg 1 5 5)))))) ((.seq ((.inst ((.fp ((.fpMovFromReg 2 7 7)))))) ((.seq ((.inst ((.fp ((.fpFma 0 1 2)))))) ((.seq ((.inst ((.fp ((.fpMovToReg 3 5 0)))))) ((.seq ((.assign 1 ((.lookup .nextFree)))) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 3)) ((.seq ((.assign 3 ((.const 281474976710671)))) ((.seq ((.store ((.var 1)) 3)) ((.seq ((.set .nextFree ((.op .add [(.var 1), (.const 16)])))) ((.assign 8 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 1)]))))))))))))))))))))))))))))), 7) =>
      true
  | _ => false

private def matches5 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (5, 0, (.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live0, .ln)))), 7) =>
      decide (live0 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches6 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (6, 0, (.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live1, .ln)))), 7) =>
      decide (live1 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches7 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (7, 0, (.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live2, .ln)))), 7) =>
      decide (live2 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches8 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (8, 0, .skip, 7) =>
      true
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0, entry1, entry2, entry3, entry4, entry5, entry6, entry7, entry8] =>
      matches0 entry0 &&
      matches1 entry1 &&
      matches2 entry2 &&
      matches3 entry3 &&
      matches4 entry4 &&
      matches5 entry5 &&
      matches6 entry6 &&
      matches7 entry7 &&
      matches8 entry8
  | _ => false

end Flapjack.Test.DataToWordFp64Oracle
