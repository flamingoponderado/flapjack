import Flapjack.Compiler.Backend.Semantics.StackSem.WordBitmap
/- Original HOL results captured in scripts/hol-probes/stacksem_word_bitmap_probe.out.
   Eleven kernel-reduced rows cover zero, terminal/trailing, bit order,
   missing continuation, continuation concatenation, and positive width one.
   These examples do not prove a universal cross-language equivalence. -/
open Flapjack.StackSem
example : bitLength (0 : BitVec 8) = 0 := by decide +kernel
example : bitLength (1 : BitVec 8) = 1 := by decide +kernel
example : bitLength (128 : BitVec 8) = 8 := by decide +kernel
example : readBitmap ([] : List (BitVec 8)) = none := by decide +kernel
example : readBitmap ([0] : List (BitVec 8)) = some [] := by decide +kernel
example : readBitmap ([1] : List (BitVec 8)) = some [] := by decide +kernel
example : readBitmap ([13] : List (BitVec 8)) = some [true,false,true] := by decide +kernel
example : readBitmap ([13,255] : List (BitVec 8)) = some [true,false,true] := by decide +kernel
example : readBitmap ([128] : List (BitVec 8)) = none := by decide +kernel
example : readBitmap ([129,5] : List (BitVec 8)) = some [true,false,false,false,false,false,false,true,false] := by decide +kernel
example : readBitmap ([1,0] : List (BitVec 1)) = some [] := by decide +kernel
