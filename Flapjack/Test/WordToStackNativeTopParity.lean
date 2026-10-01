import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile

/-! Full native top-level tuples, with identical original HOL inputs. -/
namespace Flapjack.Test.WordToStackNativeTopParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

-- wts_top_empty_plain
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 9, avoidRegs := [] } false [] =
      ([4], { bitmapsLength := 1, stackFrameSize := sptFromAList [] },
        [0], (raiseStubLocation, raiseStubNative false 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: []) := by
  simp +decide [compileNative, compileWordToStackNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_empty_perf
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 9, avoidRegs := [] } true [] =
      ([16], { bitmapsLength := 1, stackFrameSize := sptFromAList [] },
        [0], (raiseStubLocation, raiseStubNative true 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: []) := by
  simp +decide [compileNative, compileWordToStackNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_empty_zero
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 0, avoidRegs := [] } false [] =
      ([4], { bitmapsLength := 1, stackFrameSize := sptFromAList [] },
        [0], (raiseStubLocation, raiseStubNative false 0) :: (storeConstsStubLocation, storeConstsStubNative 0) :: []) := by
  simp +decide [compileNative, compileWordToStackNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_empty_narrow
example (c : AsmConfigExact 4) :
    compileNative { c with regCount := 9, avoidRegs := [] } true [] =
      ([0], { bitmapsLength := 1, stackFrameSize := sptFromAList [] },
        [0], (raiseStubLocation, raiseStubNative true 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: []) := by
  simp +decide [compileNative, compileWordToStackNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_width_one_plain
example (c : AsmConfigExact 1) :
    compileNative { c with regCount := 9, avoidRegs := [] } false [(20, 0, (.skip))] =
      ([0], { bitmapsLength := 1, stackFrameSize := sptFromAList [(20, 0)] },
        [0, 0], (raiseStubLocation, raiseStubNative false 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(20, .seq (.stackAlloc 0) (.skip))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_width_one_perf
example (c : AsmConfigExact 1) :
    compileNative { c with regCount := 9, avoidRegs := [] } true [(20, 0, (.skip))] =
      ([0], { bitmapsLength := 1, stackFrameSize := sptFromAList [(20, 0)] },
        [0, 0], (raiseStubLocation, raiseStubNative true 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(20, .seq (.stackAlloc 0) (.skip))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_zero_registers
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 0, avoidRegs := [] } false [(20, 0, (.skip))] =
      ([4], { bitmapsLength := 1, stackFrameSize := sptFromAList [(20, 2)] },
        [0, 2], (raiseStubLocation, raiseStubNative false 0) :: (storeConstsStubLocation, storeConstsStubNative 0) :: [(20, .seq (.stackAlloc 2) (.skip))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_reg_underflow
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 3, avoidRegs := [0, 1] } true [(20, 3, (.tick))] =
      ([16], { bitmapsLength := 1, stackFrameSize := sptFromAList [(20, 4)] },
        [0, 4], (raiseStubLocation, raiseStubNative true 0) :: (storeConstsStubLocation, storeConstsStubNative 0) :: [(20, .seq (.stackAlloc 1) (.tick))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_avoid_duplicate
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 7, avoidRegs := [1, 1] } false [(20, 0, (.skip))] =
      ([4], { bitmapsLength := 1, stackFrameSize := sptFromAList [(20, 2)] },
        [0, 2], (raiseStubLocation, raiseStubNative false 0) :: (storeConstsStubLocation, storeConstsStubNative 0) :: [(20, .seq (.stackAlloc 2) (.skip))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_avoid_single
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 7, avoidRegs := [1] } false [(20, 0, (.skip))] =
      ([4], { bitmapsLength := 1, stackFrameSize := sptFromAList [(20, 0)] },
        [0, 0], (raiseStubLocation, raiseStubNative false 1) :: (storeConstsStubLocation, storeConstsStubNative 1) :: [(20, .seq (.stackAlloc 0) (.skip))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_reg_only
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 9, avoidRegs := [] } false [(20, 4, (.skip))] =
      ([4], { bitmapsLength := 1, stackFrameSize := sptFromAList [(20, 0)] },
        [0, 0], (raiseStubLocation, raiseStubNative false 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(20, .seq (.stackAlloc 0) (.skip))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_stack_args
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 9, avoidRegs := [] } false [(20, 7, (.seq .skip .tick))] =
      ([4], { bitmapsLength := 1, stackFrameSize := sptFromAList [(20, 4)] },
        [0, 4], (raiseStubLocation, raiseStubNative false 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(20, .seq (.stackAlloc 1) (.seq .skip .tick))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_perf_args
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 9, avoidRegs := [] } true [(20, 7, (.mustTerminate .tick))] =
      ([16], { bitmapsLength := 1, stackFrameSize := sptFromAList [(20, 4)] },
        [0, 4], (raiseStubLocation, raiseStubNative true 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(20, .seq (.stackAlloc 1) (.tick))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_break
example (c : AsmConfigExact 8) :
    compileNative { c with regCount := 9, avoidRegs := [] } false [(20, 0, (.break 2))] =
      ([4], { bitmapsLength := 1, stackFrameSize := sptFromAList [(20, 0)] },
        [0, 0], (raiseStubLocation, raiseStubNative false 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(20, .seq (.stackAlloc 0) (.break 2))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_duplicates
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 9, avoidRegs := [] } false [(20, 7, (.skip)), (20, 0, (.tick))] =
      ([4], { bitmapsLength := 1, stackFrameSize := sptFromAList [(20, 4), (20, 0)] },
        [0, 4, 0], (raiseStubLocation, raiseStubNative false 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(20, .seq (.stackAlloc 1) (.skip)), (20, .seq (.stackAlloc 0) (.tick))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_duplicates_reverse
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 9, avoidRegs := [] } false [(20, 0, (.tick)), (20, 7, (.skip))] =
      ([4], { bitmapsLength := 1, stackFrameSize := sptFromAList [(20, 0), (20, 4)] },
        [0, 0, 4], (raiseStubLocation, raiseStubNative false 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(20, .seq (.stackAlloc 0) (.tick)), (20, .seq (.stackAlloc 1) (.skip))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_order
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 9, avoidRegs := [] } true [(20, 7, (.skip)), (21, 0, (.tick)), (22, 5, (.seq .skip .tick))] =
      ([16], { bitmapsLength := 1, stackFrameSize := sptFromAList [(20, 4), (21, 0), (22, 2)] },
        [0, 4, 0, 2], (raiseStubLocation, raiseStubNative true 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(20, .seq (.stackAlloc 1) (.skip)), (21, .seq (.stackAlloc 0) (.tick)), (22, .seq (.stackAlloc 1) (.seq .skip .tick))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_large_identifier
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 9, avoidRegs := [] } false [(18446744073709551617, 0, (.skip))] =
      ([4], { bitmapsLength := 1, stackFrameSize := sptFromAList [(18446744073709551617, 0)] },
        [0, 0], (raiseStubLocation, raiseStubNative false 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(18446744073709551617, .seq (.stackAlloc 0) (.skip))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, appListAppend, appendAux] <;> decide +kernel

-- wts_top_bitmap_plain
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 9, avoidRegs := [] } false [(20, 5, (.alloc 0 (.ln, .ln)))] =
      ([4, 2], { bitmapsLength := 2, stackFrameSize := sptFromAList [(20, 2)] },
        [0, 2], (raiseStubLocation, raiseStubNative false 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(20, .seq (.stackAlloc 1) (.seq (.seq (.inst (.const 4 2)) (.stackStore 4 0)) (.alloc 1)))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- wts_top_bitmap_perf
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 9, avoidRegs := [] } true [(20, 5, (.alloc 0 (.ln, .ln)))] =
      ([16, 2], { bitmapsLength := 2, stackFrameSize := sptFromAList [(20, 2)] },
        [0, 2], (raiseStubLocation, raiseStubNative true 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(20, .seq (.stackAlloc 1) (.seq (.seq (.inst (.const 4 2)) (.stackStore 4 0)) (.alloc 1)))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- wts_top_bitmap_order
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 9, avoidRegs := [] } false [(20, 5, (.alloc 0 (.ln, .ln))), (21, 7, (.alloc 0 (.ln, .ln)))] =
      ([4, 2, 8], { bitmapsLength := 3, stackFrameSize := sptFromAList [(20, 2), (21, 4)] },
        [0, 2, 4], (raiseStubLocation, raiseStubNative false 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(20, .seq (.stackAlloc 1) (.seq (.seq (.inst (.const 4 2)) (.stackStore 4 0)) (.alloc 1))), (21, .seq (.stackAlloc 1) (.seq (.seq (.inst (.const 4 3)) (.stackStore 4 0)) (.alloc 1)))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- wts_top_bitmap_reverse
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 9, avoidRegs := [] } false [(20, 7, (.alloc 0 (.ln, .ln))), (21, 5, (.alloc 0 (.ln, .ln)))] =
      ([4, 8, 2], { bitmapsLength := 3, stackFrameSize := sptFromAList [(20, 4), (21, 2)] },
        [0, 4, 2], (raiseStubLocation, raiseStubNative false 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(20, .seq (.stackAlloc 1) (.seq (.seq (.inst (.const 4 2)) (.stackStore 4 0)) (.alloc 1))), (21, .seq (.stackAlloc 1) (.seq (.seq (.inst (.const 4 3)) (.stackStore 4 0)) (.alloc 1)))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- wts_top_bitmap_multiword
example (c : AsmConfigExact 8) :
    compileNative { c with regCount := 9, avoidRegs := [] } false [(20, 12, (.alloc 0 (.ln, .ln))), (21, 5, (.alloc 0 (.ln, .ln)))] =
      ([4, 128, 2, 2], { bitmapsLength := 4, stackFrameSize := sptFromAList [(20, 9), (21, 2)] },
        [0, 9, 2], (raiseStubLocation, raiseStubNative false 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(20, .seq (.stackAlloc 1) (.seq (.seq (.inst (.const 4 2)) (.stackStore 4 0)) (.alloc 1))), (21, .seq (.stackAlloc 1) (.seq (.seq (.inst (.const 4 4)) (.stackStore 4 0)) (.alloc 1)))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- wts_top_bitmap_zero_frame
example (c : AsmConfigExact 64) :
    compileNative { c with regCount := 9, avoidRegs := [] } false [(20, 0, (.alloc 0 (.ln, .ln))), (21, 5, (.alloc 0 (.ln, .ln)))] =
      ([4, 2], { bitmapsLength := 2, stackFrameSize := sptFromAList [(20, 0), (21, 2)] },
        [0, 0, 2], (raiseStubLocation, raiseStubNative false 4) :: (storeConstsStubLocation, storeConstsStubNative 4) :: [(20, .seq (.stackAlloc 0) (.seq .skip (.alloc 1))), (21, .seq (.stackAlloc 1) (.seq (.seq (.inst (.const 4 2)) (.stackStore 4 0)) (.alloc 1)))]) := by
  simp +decide [compileNative, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

end Flapjack.Test.WordToStackNativeTopParity
