import Flapjack.RiscV.WordCse

/-! Original key_load_* and key_heap_* observations at production callers.
These are routing correspondences, not a CSE simulation theorem. -/
namespace Flapjack.Test.WordCseProductionLoadHeapKeys
open Flapjack Flapjack.RiscV

-- Arbitrary width and memory operator; no bounds or representation premises.
example {width : Nat} [NeZero width] (operator : WordMemOp) (address : Nat)
    (offset : BitVec width) :
    wordCseLoadOffsetToNumList operator address offset =
      Compiler.Backend.WordCse.loadToNumList operator address offset :=
  wordCseLoadOffsetToNumList_native operator address offset

-- Offset-free production instructions and explicit zero offsets share a key.
example {width : Nat} [NeZero width] (operator : WordMemOp) (address : Nat) :
    wordCseLoadOffsetToNumList operator address (0 : BitVec width) =
      wordCseLoadToNumList operator address := by rfl

example (operator : BinOp) (source : Nat) :
    wordCseHeapToNumList operator source =
      Compiler.Backend.WordCse.opCurrHeapToNumList operator source := rfl

-- Original key_load_load.
example : wordCseLoadOffsetToNumList .load 9 (255 : BitVec 8) = [21,109,255] := by rfl

-- Original key_load_load8.
example : wordCseLoadOffsetToNumList .load8 9 (255 : BitVec 8) = [22,109,255] := by rfl

-- Original key_load_load16.
example : wordCseLoadOffsetToNumList .load16 9 (255 : BitVec 8) = [46,109,255] := by rfl

-- Original key_load_load32.
example : wordCseLoadOffsetToNumList .load32 9 (255 : BitVec 8) = [44,109,255] := by rfl

-- Original key_load_store.
example : wordCseLoadOffsetToNumList .store 9 (255 : BitVec 8) = [23,109,255] := by rfl

-- Original key_load_store8.
example : wordCseLoadOffsetToNumList .store8 9 (255 : BitVec 8) = [47,109,255] := by rfl

-- Original key_load_store16.
example : wordCseLoadOffsetToNumList .store16 9 (255 : BitVec 8) = [24,109,255] := by rfl

-- Original key_load_store32.
example : wordCseLoadOffsetToNumList .store32 9 (255 : BitVec 8) = [45,109,255] := by rfl

-- Original key_heap_add.
example : wordCseHeapToNumList .add 7 = [0,35,107] := by rfl

-- Original key_heap_sub.
example : wordCseHeapToNumList .sub 7 = [0,36,107] := by rfl

-- Original key_heap_and.
example : wordCseHeapToNumList .and 7 = [0,37,107] := by rfl

-- Original key_heap_or.
example : wordCseHeapToNumList .or 7 = [0,38,107] := by rfl

-- Original key_heap_xor.
example : wordCseHeapToNumList .xor 7 = [0,39,107] := by rfl

-- Generic diagnostic words remain unbounded, without machine truncation.
example : wordCseLoadOffsetToNumList .load 9 (2 ^ 80 + 7 : Nat) =
    [21,109,2 ^ 80 + 7] := rfl

#print axioms wordCseLoadOffsetToNumList_native
end Flapjack.Test.WordCseProductionLoadHeapKeys
