import Flapjack.Compiler.Backend.WordToStack.NativePrograms

/-! Identical inputs and observations from the original native wrapper probes. -/
namespace Flapjack.Test.WordToStackNativeProgramsParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

-- wts_prog_zero_registers
example  (c : AsmConfigExact 64) :
    compileProgNative c false (.skip) 0 0 (.list [4],1) = (.seq (.stackAlloc 2) .skip,2,(.list [4],1)) := by
  simp +decide [compileProgNative, maxVarHOL, compNative] <;> decide +kernel

-- wts_prog_register_only
example  (c : AsmConfigExact 64) :
    compileProgNative c false (.skip) 0 4 (.list [4],1) = (.seq (.stackAlloc 0) .skip,0,(.list [4],1)) := by
  simp +decide [compileProgNative, maxVarHOL, compNative] <;> decide +kernel

-- wts_prog_exact_register_args
example  (c : AsmConfigExact 64) :
    compileProgNative c false (.skip) 4 4 (.list [4],1) = (.seq (.stackAlloc 0) .skip,0,(.list [4],1)) := by
  simp +decide [compileProgNative, maxVarHOL, compNative] <;> decide +kernel

-- wts_prog_first_stack_arg
example  (c : AsmConfigExact 64) :
    compileProgNative c false (.skip) 5 4 (.list [4],1) = (.seq (.stackAlloc 1) .skip,2,(.list [4],1)) := by
  simp +decide [compileProgNative, maxVarHOL, compNative] <;> decide +kernel

-- wts_prog_three_stack_args
example  (c : AsmConfigExact 64) :
    compileProgNative c false (.skip) 7 4 (.list [4],1) = (.seq (.stackAlloc 1) .skip,4,(.list [4],1)) := by
  simp +decide [compileProgNative, maxVarHOL, compNative] <;> decide +kernel

-- wts_prog_all_stack_args
example  (c : AsmConfigExact 64) :
    compileProgNative c false (.skip) 3 0 (.list [4],1) = (.seq (.stackAlloc 1) .skip,4,(.list [4],1)) := by
  simp +decide [compileProgNative, maxVarHOL, compNative] <;> decide +kernel

-- wts_prog_huge_register_count
example  (c : AsmConfigExact 64) :
    compileProgNative c false (.skip) 0 99 (.list [4],1) = (.seq (.stackAlloc 0) .skip,0,(.list [4],1)) := by
  simp +decide [compileProgNative, maxVarHOL, compNative] <;> decide +kernel

-- wts_prog_var_boundary
example  (c : AsmConfigExact 64) :
    compileProgNative c false (.assign 6 (.const 9)) 0 4 (.list [4],1) = (.seq (.stackAlloc 0) .skip,0,(.list [4],1)) := by
  simp +decide [compileProgNative, maxVarHOL, maxVarExpHOL, compNative] <;> decide +kernel

-- wts_prog_var_first_stack
example  (c : AsmConfigExact 64) :
    compileProgNative c false (.assign 8 (.const 9)) 0 4 (.list [4],1) = (.seq (.stackAlloc 2) .skip,2,(.list [4],1)) := by
  simp +decide [compileProgNative, maxVarHOL, maxVarExpHOL, compNative] <;> decide +kernel

-- wts_prog_var_odd_stack
example  (c : AsmConfigExact 64) :
    compileProgNative c false (.assign 9 (.const 9)) 0 4 (.list [4],1) = (.seq (.stackAlloc 2) .skip,2,(.list [4],1)) := by
  simp +decide [compileProgNative, maxVarHOL, maxVarExpHOL, compNative] <;> decide +kernel

-- wts_prog_vars_exceed_args
example  (c : AsmConfigExact 64) :
    compileProgNative c false (.assign 16 (.const 9)) 5 4 (.list [4],1) = (.seq (.stackAlloc 5) .skip,6,(.list [4],1)) := by
  simp +decide [compileProgNative, maxVarHOL, maxVarExpHOL, compNative] <;> decide +kernel

-- wts_prog_args_exceed_vars
example  (c : AsmConfigExact 8) :
    compileProgNative c false (.assign 8 (.const 9)) 12 4 (.list [4],1) = (.seq (.stackAlloc 1) .skip,9,(.list [4],1)) := by
  simp +decide [compileProgNative, maxVarHOL, maxVarExpHOL, compNative] <;> decide +kernel

-- wts_prog_perf_tick
example  (c : AsmConfigExact 64) :
    compileProgNative c true (.tick) 7 4 (.list [4],1) = (.seq (.stackAlloc 1) .tick,4,(.list [4],1)) := by
  simp +decide [compileProgNative, maxVarHOL, compNative] <;> decide +kernel

-- wts_prog_width_one
example  (c : AsmConfigExact 1) :
    compileProgNative c false (.skip) 7 4 (.list [4],1) = (.seq (.stackAlloc 1) .skip,4,(.list [4],1)) := by
  simp +decide [compileProgNative, maxVarHOL, compNative] <;> decide +kernel

-- wts_prog_list_empty
example  (c : AsmConfigExact 64) :
    compileWordToStackNative c false 4 ([] : List (Bool × Nat × WordLangProgHOL (BitVec 64))) (.list [4],1) = ([],[],(.list [4],1)) := by
  simp +decide [compileWordToStackNative] <;> decide +kernel

-- wts_prog_list_generic
example {β : Type} (i j : β) (c : AsmConfigExact 64) :
    compileWordToStackNative c false 4 [(i,7,.skip),(j,0,.tick)] (.list [4],1) = ([(i,.seq (.stackAlloc 1) .skip),(j,.seq (.stackAlloc 0) .tick)],[4,0],(.list [4],1)) := by
  simp +decide [compileProgNative, compileWordToStackNative, maxVarHOL, compNative] <;> decide +kernel

-- wts_prog_list_duplicates
example  (c : AsmConfigExact 64) :
    compileWordToStackNative c true 4 [(true,7,.skip),(true,0,.tick)] (.list [4],1) = ([(true,.seq (.stackAlloc 1) .skip),(true,.seq (.stackAlloc 0) .tick)],[4,0],(.list [4],1)) := by
  simp +decide [compileProgNative, compileWordToStackNative, maxVarHOL, compNative] <;> decide +kernel

-- wts_prog_bitmap_order
example  (c : AsmConfigExact 64) :
    let (ps,fs,bs) := compileWordToStackNative c false 4 [(0,5,.alloc 0 (.ln,.ln)), (1,7,.alloc 0 (.ln,.ln))] (.list [4],1); ps.map Prod.fst=[0,1] ∧ fs=[2, 4] ∧ appListAppend bs.1=[4, 2, 8] ∧ bs.2=3 := by
  simp +decide [compileProgNative, compileWordToStackNative, maxVarHOL, maxList, cutsetsMaxHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- wts_prog_bitmap_reverse
example  (c : AsmConfigExact 64) :
    let (ps,fs,bs) := compileWordToStackNative c false 4 [(0,7,.alloc 0 (.ln,.ln)), (1,5,.alloc 0 (.ln,.ln))] (.list [4],1); ps.map Prod.fst=[0,1] ∧ fs=[4, 2] ∧ appListAppend bs.1=[4, 8, 2] ∧ bs.2=3 := by
  simp +decide [compileProgNative, compileWordToStackNative, maxVarHOL, maxList, cutsetsMaxHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- wts_prog_bitmap_multiword
example  (c : AsmConfigExact 8) :
    let (ps,fs,bs) := compileWordToStackNative c false 4 [(0,12,.alloc 0 (.ln,.ln)), (1,5,.alloc 0 (.ln,.ln))] (.list [4],1); ps.map Prod.fst=[0,1] ∧ fs=[9, 2] ∧ appListAppend bs.1=[4, 128, 2, 2] ∧ bs.2=4 := by
  simp +decide [compileProgNative, compileWordToStackNative, maxVarHOL, maxList, cutsetsMaxHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- wts_prog_bitmap_zero_frame
example  (c : AsmConfigExact 64) :
    let (ps,fs,bs) := compileWordToStackNative c false 4 [(0,0,.alloc 0 (.ln,.ln)), (1,5,.alloc 0 (.ln,.ln))] (.list [4],1); ps.map Prod.fst=[0,1] ∧ fs=[0, 2] ∧ appListAppend bs.1=[4, 2] ∧ bs.2=2 := by
  simp +decide [compileProgNative, compileWordToStackNative, maxVarHOL, maxList, cutsetsMaxHOL, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

end Flapjack.Test.WordToStackNativeProgramsParity
