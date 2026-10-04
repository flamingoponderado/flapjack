import Flapjack.Compiler.Backend.StackAlloc.Proofs.GcBitmaps

/-!
# `stack_allocProof` GC bitmap definitions: original-oracle rows

Kernel replay of `scripts/hol-probes/stack_alloc_gc_bitmaps_probe.out` (64-bit
`word_gc_move_bitmap`, `word_gc_move_bitmaps` and `word_gc_move_roots_bitmaps`);
memories are compared at the probed addresses.
-/

namespace Flapjack.Test.StackAllocGcBitmapsParity

open Flapjack Flapjack.StackSem Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.WordGcFunctions Flapjack.Compiler.Backend.StackAlloc

private def conf : Config :=
  { tagBits := 1, lenBits := 2, padBits := 3, lenSize := 16, hasDiv := false,
    hasLongdiv := false, be := false,
    callEmptyFfi := false, gcKind := .simple }

private def mem : BitVec 64 → WordLocW 64 :=
  fun a => if a = 1008 then .word 0x1000000000002 else .word a

private def stk : List (WordLocW 64) := [.word 0x101, .word 4, .word 7, .word 9]

private def univ : BitVec 64 → Bool := fun _ => true

private theorem getBits13 : getBits (13#64) = [true, false, true] := by
  simp [getBits, bitLength_eq]; decide

private theorem readBitmap13 : readBitmap [13#64] = some [true, false, true] := by
  rw [readBitmap]; simp [bitLength_eq]; decide

attribute [local simp] wordGcMoveBitmap wordGcMoveBitmaps wordGcMoveRootsBitmaps getBits13
  readBitmap13 filterBitmap mapBitmap wordGcMoveRoots_nil wordGcMoveRoots_cons wordGcMove
  ptrToAddr shiftLength wordSemBytesInWord wordSemIsFwdPtr wordSemTheWord wordSemIsWordLoc
  decodeLength updateAddr smallShiftLength gcWordBitsLow gcUpdate memcpy_zero memcpy_of_ne
  fullReadBitmap stk mem univ conf

-- gcb_bitmap=SOME ([Word 1793w; Word 4w; Word 64007w],[Word 9w],9w,2016w,Word 28w,T)
example :
    (match wordGcMoveBitmap conf ((13 : BitVec 64), stk, (7 : BitVec 64), 2000, 1000, mem, univ) with
     | none => none
     | some (hd, ws, i, pa, m, c) => some (hd, ws, i, pa, m 1008, c)) =
      some ([.word 1793, .word 4, .word 64007], [.word 9], 9, 2016, .word 28, true) := by
  simp

-- gcb_bitmap_short=NONE
example :
    (wordGcMoveBitmap conf ((13 : BitVec 64), [.word 4], (7 : BitVec 64), 2000, 1000, mem, univ)) =
      none := by
  simp

-- gcb_bitmaps=SOME ([Word 1793w; Word 4w; Word 64007w],[Word 9w],9w,2016w,T)
example :
    (match wordGcMoveBitmaps conf ((.word 1 : WordLocW 64), stk, [(13 : BitVec 64)],
        (7 : BitVec 64), 2000, 1000, mem, univ) with
     | none => none
     | some (hd, ws, i, pa, _, c) => some (hd, ws, i, pa, c)) =
      some ([.word 1793, .word 4, .word 64007], [.word 9], 9, 2016, true) := by
  simp

-- gcb_bitmaps_zero=NONE
example :
    wordGcMoveBitmaps conf ((.word 0 : WordLocW 64), stk, [(13 : BitVec 64)],
        (7 : BitVec 64), 2000, 1000, mem, univ) = none := by
  simp

-- gcb_roots_bitmaps=([Word 1w; Word 1793w; Word 4w; Word 64007w; Word 0w],9w,2016w,T)
example :
    (let (st, i, pa, _, c) := wordGcMoveRootsBitmaps conf
        ([.word 1, .word 0x101, .word 4, .word 7, .word 0], [(13 : BitVec 64)],
          (7 : BitVec 64), 2000, 1000, mem, univ)
     (st, i, pa, c)) =
      ([.word 1, .word 1793, .word 4, .word 64007, .word 0], 9, 2016, true) := by
  simp [encStack, decStack]

def runChecks : IO Bool := do
  IO.println "PASS stack_allocProof word_gc_move_bitmap(s)/roots_bitmaps match five original HOL rows"
  pure true

end Flapjack.Test.StackAllocGcBitmapsParity
