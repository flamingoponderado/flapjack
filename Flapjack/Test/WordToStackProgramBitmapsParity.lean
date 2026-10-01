import Flapjack.Compiler.Backend.WordToStack.Proofs.ProgramBitmaps

/-! Kernel replay of the ten original rows in
scripts/hol-probes/word_to_stack_program_bitmaps_probe.out.
These finite observations do not prove cross-language equivalence. -/
namespace Flapjack.Test.WordToStackProgramBitmapsParity
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

/-- Flapjack-only observation matching the original single-program probe. -/
private def singleSnapshot {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (p : WordLangProgHOL (BitVec width)) (arguments index : Nat) :
    Nat × Nat × Nat × Bool × Nat :=
  let (_, frame, bm, next) := compileProgNative c false p arguments 4
    (.append (.list [8]) (.list [2]), index)
  let words := appListAppend bm
  (words.length, next, next - words.length, decide (words.take 2 = [8,2]), frame)

/-- Flapjack-only row observer retaining frame sizes and duplicate keys. -/
private def rowsSnapshot {width : Nat} [NeZero width] {β : Type}
    (c : AsmConfigExact width) (rows : List (β × Nat × WordLangProgHOL (BitVec width))) :
    Nat × Nat × Nat × Bool × List Nat × List β :=
  let (programs, frames, bm, next) := compileWordToStackNative c false 4 rows
    (.append (.list [8]) (.list [2]), 5)
  let words := appListAppend bm
  (words.length, next, next - words.length, decide (words.take 2 = [8,2]), frames,
    programs.map Prod.fst)

-- pb_single_skip
example (c : AsmConfigExact 64) :
    singleSnapshot c (.skip) 0 5 = (2, 5, 3, true, 0) := by
  simp +decide [singleSnapshot, compileProgNative, maxVarHOL, compNative, appListAppend, appendAux] <;> decide +kernel

-- pb_single_zero_frame
example (c : AsmConfigExact 64) :
    singleSnapshot c (.alloc 0 (.ln,.ln)) 0 5 = (2, 5, 3, true, 0) := by
  simp +decide [singleSnapshot, compileProgNative, maxVarHOL, compNative, wLiveNative, appListAppend, appendAux] <;> decide +kernel

-- pb_single_alloc
example (c : AsmConfigExact 64) :
    singleSnapshot c (.alloc 0 (.ln,.ln)) 5 5 = (3, 6, 3, true, 2) := by
  simp +decide [singleSnapshot, compileProgNative, maxVarHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- pb_single_seq
example (c : AsmConfigExact 64) :
    singleSnapshot c (.seq (.alloc 0 (.ln,.ln)) (.alloc 0 (.ln,.ln))) 5 5 = (4, 7, 3, true, 2) := by
  simp +decide [singleSnapshot, compileProgNative, maxVarHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- pb_single_invalid_bound
example (c : AsmConfigExact 64) :
    singleSnapshot c (.alloc 0 (.ln,.ln)) 5 1 = (3, 2, 0, true, 2) := by
  simp +decide [singleSnapshot, compileProgNative, maxVarHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- pb_single_width_one
example (c : AsmConfigExact 1) :
    singleSnapshot c (.alloc 0 (.ln,.ln)) 5 5 = (3, 6, 3, true, 2) := by
  simp +decide [singleSnapshot, compileProgNative, maxVarHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- pb_rows_empty
example (c : AsmConfigExact 64) :
    rowsSnapshot c ([] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) =
      (2, 5, 3, true, [], []) := by
  simp +decide [rowsSnapshot, compileWordToStackNative, appListAppend, appendAux] <;> decide +kernel

-- pb_rows_repeat_id
example (c : AsmConfigExact 64) :
    rowsSnapshot c ([(7,5,.alloc 0 (.ln,.ln)),(7,5,.alloc 0 (.ln,.ln))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) =
      (4, 7, 3, true, [2,2], [7,7]) := by
  simp +decide [rowsSnapshot, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- pb_rows_mixed
example (c : AsmConfigExact 64) :
    rowsSnapshot c ([(8,0,.skip),(9,5,.alloc 0 (.ln,.ln)),(10,5,.seq (.alloc 0 (.ln,.ln)) (.alloc 0 (.ln,.ln)))] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) =
      (5, 8, 3, true, [0,2,2], [8,9,10]) := by
  simp +decide [rowsSnapshot, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- pb_rows_bool
example (c : AsmConfigExact 8) :
    rowsSnapshot c ([(true,5,.alloc 0 (.ln,.ln)),(false,0,.skip)] : List (Bool × Nat × WordLangProgHOL (BitVec 8))) =
      (3, 6, 3, true, [2,0], [true,false]) := by
  simp +decide [rowsSnapshot, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

end Flapjack.Test.WordToStackProgramBitmapsParity
