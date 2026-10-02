import Flapjack.Compiler.Backend.WordGcFunctions

/-!
# `word_gcFunctions`: original-oracle rows

Kernel replay of the rows of `scripts/hol-probes/word_gc_functions_probe.out`
(original HOL `EVAL` of the `word_gcFunctionsScript.sml` definitions at
`:64` words).  Memory results are compared at the probed addresses.
-/

namespace Flapjack.Test.WordGcFunctionsParity

open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions

private def conf : Config :=
  { tagBits := 1, lenBits := 2, padBits := 3, lenSize := 16, hasDiv := false,
    hasLongdiv := false, hasFpOps := false, hasFpTern := false, be := false,
    callEmptyFfi := false, gcKind := .simple }

private def mem : BitVec 64 → WordLocW 64 :=
  fun a => if a = 1008 then .word 0x1000000000002 else .word a

private def fwd : BitVec 64 → WordLocW 64 :=
  fun a => if a = 1008 then .word 0x40 else .word a

private def refMem : BitVec 64 → WordLocW 64 :=
  fun a => if a = 1008 then .word 0x100000000000A else .word a

private def listMem : BitVec 64 → WordLocW 64 :=
  fun a => if a = 1008 then .word 0x1000000000002 else if a = 500 then .word 0x101 else .word 4

private def univ : BitVec 64 → Bool := fun _ => true

-- gc_ptr_to_addr=1144w
example : ptrToAddr conf (1000 : BitVec 64) 0x1234 = 1144 := by
  simp [ptrToAddr, shiftLength, conf, wordSemBytesInWord]
-- gc_update_addr=1287w
example : updateAddr conf (5 : BitVec 64) 0x1237 = 1287 := by
  simp [updateAddr, shiftLength, smallShiftLength, gcWordBitsLow, conf]
-- gc_decode_length=3w
example : decodeLength conf (0x3000000000002 : BitVec 64) = 3 := by
  simp [decodeLength, conf]
-- gc_is_ref_header_8=T
example : isRefHeader (8 : BitVec 64) = true := by decide
-- gc_is_ref_header_c=F
example : isRefHeader (12 : BitVec 64) = false := by decide
-- gc_memcpy=(216w,Word 100w,Word 108w,Word 216w,T)
example :
    (let (b, m1, c) := memcpy (2 : BitVec 64) 100 200 (fun a => .word a) univ
     (b, m1 200, m1 208, m1 216, c)) = (216, .word 100, .word 108, .word 216, true) := by
  simp [memcpy_zero, memcpy_of_ne, gcUpdate, wordSemBytesInWord, univ]
-- gc_memcpy_dom=F
example :
    (let (_, _, c) := memcpy (2 : BitVec 64) 100 200 (fun a => .word a)
        (fun a => a = 100 ∨ a = 200 ∨ a = 108)
     c) = false := by
  simp [memcpy_zero, memcpy_of_ne, gcUpdate, wordSemBytesInWord]

section move
attribute [local simp] wordGcMove wordGenGcMove wordGenGcPartialMove ptrToAddr shiftLength
  wordSemBytesInWord wordSemIsFwdPtr wordSemTheWord wordSemIsWordLoc decodeLength updateAddr
  smallShiftLength gcWordBitsLow gcUpdate memcpy_zero memcpy_of_ne isRefHeader univ

-- gc_move_loc=(Loc 3 0,7w,2000w,T)
example :
    (let (w1, i1, pa1, _, c) := wordGcMove conf (.loc 3 0, (7 : BitVec 64), 2000, 1000,
        fun a => .word a, univ)
     (w1, i1, pa1, c)) = (.loc 3 0, 7, 2000, true) := by simp
-- gc_move_loc_nonzero=(Loc 3 4,7w,2000w,F)
example :
    (let (w1, i1, pa1, _, c) := wordGcMove conf (.loc 3 4, (7 : BitVec 64), 2000, 1000,
        fun a => .word a, univ)
     (w1, i1, pa1, c)) = (.loc 3 4, 7, 2000, false) := by simp
-- gc_move_small=(Word 4w,7w,2000w,T)
example :
    (let (w1, i1, pa1, _, c) := wordGcMove conf (.word 4, (7 : BitVec 64), 2000, 1000,
        fun a => .word a, univ)
     (w1, i1, pa1, c)) = (.word 4, 7, 2000, true) := by simp
-- gc_move_copy=(Word 1793w,9w,2016w,Word 28w,Word 0x1000000000002w,Word 1016w,T)
example :
    (let (w1, i1, pa1, m1, c) := wordGcMove conf (.word 0x101, (7 : BitVec 64), 2000, 1000, mem,
        univ)
     (w1, i1, pa1, m1 1008, m1 2000, m1 2008, c)) =
      (.word 1793, 9, 2016, .word 28, .word 0x1000000000002, .word 1016, true) := by
  simp [mem, conf]
-- gc_move_fwd=(Word 4097w,7w,2000w,Word 64w,T)
example :
    (let (w1, i1, pa1, m1, c) := wordGcMove conf (.word 0x101, (7 : BitVec 64), 2000, 1000, fwd,
        univ)
     (w1, i1, pa1, m1 1008, c)) = (.word 4097, 7, 2000, .word 64, true) := by
  simp [fwd, conf]
-- gc_gen_move_copy=(Word 1793w,9w,2016w,50w,3000w,Word 28w,Word 0x1000000000002w,T)
example :
    (let (w1, i1, pa1, ib1, pb1, m1, c) := wordGenGcMove conf (.word 0x101, (7 : BitVec 64),
        2000, 50, 3000, 1000, mem, univ)
     (w1, i1, pa1, ib1, pb1, m1 1008, m1 2000, c)) =
      (.word 1793, 9, 2016, 50, 3000, .word 28, .word 0x1000000000002, true) := by
  simp [mem, conf]
-- gc_gen_move_ref=(Word 12289w,7w,2000w,48w,2984w,Word 192w,Word 0x100000000000Aw,
--  Word 1016w,T)
example :
    (let (w1, i1, pa1, ib1, pb1, m1, c) := wordGenGcMove conf (.word 0x101, (7 : BitVec 64),
        2000, 50, 3000, 1000, refMem, univ)
     (w1, i1, pa1, ib1, pb1, m1 1008, m1 2984, m1 2992, c)) =
      (.word 12289, 7, 2000, 48, 2984, .word 192, .word 0x100000000000A, .word 1016, true) := by
  simp [refMem, conf]
-- gc_partial_move_outside=(Word 257w,7w,2000w,T)
example :
    (let (w1, i1, pa1, _, c) := wordGenGcPartialMove conf (.word 0x101, (7 : BitVec 64), 2000,
        1000, mem, univ, 16, 32)
     (w1, i1, pa1, c)) = (.word 257, 7, 2000, true) := by
  simp [conf]
-- gc_partial_move_inside=(Word 1793w,9w,2016w,Word 28w,T)
example :
    (let (w1, i1, pa1, m1, c) := wordGenGcPartialMove conf (.word 0x101, (7 : BitVec 64), 2000,
        1000, mem, univ, 8, 32)
     (w1, i1, pa1, m1 1008, c)) = (.word 1793, 9, 2016, .word 28, true) := by
  simp [mem, conf]
-- gc_move_roots=([Word 4w; Loc 1 0; Word 1793w],9w,2016w,T)
example :
    (let (ws, i1, pa1, _, c) := wordGcMoveRoots conf ([.word 4, .loc 1 0, .word 0x101],
        (7 : BitVec 64), 2000, 1000, mem, univ)
     (ws, i1, pa1, c)) = ([.word 4, .loc 1 0, .word 1793], 9, 2016, true) := by
  simp [wordGcMoveRoots, mem, conf]
-- gc_move_list=(516w,9w,2016w,Word 1793w,Word 4w,T)
example :
    (let (a2, i1, pa1, m1, c) := wordGcMoveList conf ((500 : BitVec 64), 2, 7, 2000, 1000,
        listMem, univ)
     (a2, i1, pa1, m1 500, m1 508, c)) = (516, 9, 2016, .word 1793, .word 4, true) := by
  simp [wordGcMoveList_zero, wordGcMoveList_of_ne, listMem, conf]

end move

-- gc_glob_real=Word 1016w
example : globReal conf (1000 : BitVec 64) (.word 0x200) = .word 1016 := by
  simp [globReal, shiftLength, conf, wordShiftAmount]
-- gc_glob_real_loc=Loc 2 3
example : globReal conf (1000 : BitVec 64) (.loc 2 3) = .loc 2 3 := rfl
-- gc_new_trig_small=80w
example : newTrig (100 : BitVec 64) 8 [10] = 80 := by
  simp [newTrig, getGenSize, wordSemBytesInWord]
-- gc_new_trig_big=100w
example : newTrig (100 : BitVec 64) 200 [1] = 100 := by
  simp [newTrig, getGenSize, wordSemBytesInWord]
-- gc_new_trig_aligned=200w
example : newTrig (1000 : BitVec 64) 200 [1] = 200 := by
  simp [newTrig, getGenSize, wordSemBytesInWord, gcByteAligned]
-- gc_new_trig_unaligned=1000w
example : newTrig (1000 : BitVec 64) 201 [1] = 1000 := by
  simp [newTrig, getGenSize, wordSemBytesInWord, gcByteAligned]

def runChecks : IO Bool := do
  IO.println "PASS word_gcFunctions GC definitions match 24 original HOL rows"
  pure true

end Flapjack.Test.WordGcFunctionsParity
