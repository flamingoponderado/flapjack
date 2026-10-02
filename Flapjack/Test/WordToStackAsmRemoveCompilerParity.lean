import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmRemoveCompiler

namespace Flapjack.Test.WordToStackAsmRemoveCompilerParity
open Flapjack Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open Flapjack.WordToStackProofs.AsmRemoveCompiler
/- Fresh full original theorem and source guard applications, covering all26
source constructors at frames0/4. No post-allocation or minimum-frame premise.
Regression evidence only, not cross-language equivalence. -/

-- arc_1_0_skip_guard, arc_1_0_skip_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.skip : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_move_guard, arc_1_0_move_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_inst_guard, arc_1_0_inst_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_assign_guard, arc_1_0_assign_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_get_guard, arc_1_0_get_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_set_guard, arc_1_0_set_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_store_guard, arc_1_0_store_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_alloc_guard, arc_1_0_alloc_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_consts_guard, arc_1_0_consts_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_raise_guard, arc_1_0_raise_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.raise 99 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_return_guard, arc_1_0_return_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_break_guard, arc_1_0_break_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.break 777 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_continue_guard, arc_1_0_continue_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.continue 777 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_tick_guard, arc_1_0_tick_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.tick : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_heap_guard, arc_1_0_heap_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_loc_guard, arc_1_0_loc_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_install_guard, arc_1_0_install_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_code_guard, arc_1_0_code_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_data_guard, arc_1_0_data_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_ffi_guard, arc_1_0_ffi_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_share_guard, arc_1_0_share_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_must_guard, arc_1_0_must_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_loop_guard, arc_1_0_loop_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_seq_guard, arc_1_0_seq_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_if_guard, arc_1_0_if_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_tail_guard, arc_1_0_tail_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_callreturn_guard, arc_1_0_callreturn_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_0_callhandler_guard, arc_1_0_callhandler_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_skip_guard, arc_1_4_skip_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.skip : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_move_guard, arc_1_4_move_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_inst_guard, arc_1_4_inst_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_assign_guard, arc_1_4_assign_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_get_guard, arc_1_4_get_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_set_guard, arc_1_4_set_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_store_guard, arc_1_4_store_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_alloc_guard, arc_1_4_alloc_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_consts_guard, arc_1_4_consts_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_raise_guard, arc_1_4_raise_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.raise 99 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_return_guard, arc_1_4_return_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_break_guard, arc_1_4_break_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.break 777 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_continue_guard, arc_1_4_continue_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.continue 777 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_tick_guard, arc_1_4_tick_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.tick : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_heap_guard, arc_1_4_heap_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_loc_guard, arc_1_4_loc_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_install_guard, arc_1_4_install_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_code_guard, arc_1_4_code_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_data_guard, arc_1_4_data_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_ffi_guard, arc_1_4_ffi_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_share_guard, arc_1_4_share_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_must_guard, arc_1_4_must_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_loop_guard, arc_1_4_loop_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_seq_guard, arc_1_4_seq_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_if_guard, arc_1_4_if_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_tail_guard, arc_1_4_tail_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_callreturn_guard, arc_1_4_callreturn_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_1_4_callhandler_guard, arc_1_4_callhandler_result
example (conf : AsmConfigExact 1) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 1)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_skip_guard, arc_2_0_skip_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.skip : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_move_guard, arc_2_0_move_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_inst_guard, arc_2_0_inst_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_assign_guard, arc_2_0_assign_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_get_guard, arc_2_0_get_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_set_guard, arc_2_0_set_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_store_guard, arc_2_0_store_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_alloc_guard, arc_2_0_alloc_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_consts_guard, arc_2_0_consts_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_raise_guard, arc_2_0_raise_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.raise 99 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_return_guard, arc_2_0_return_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_break_guard, arc_2_0_break_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.break 777 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_continue_guard, arc_2_0_continue_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.continue 777 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_tick_guard, arc_2_0_tick_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.tick : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_heap_guard, arc_2_0_heap_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_loc_guard, arc_2_0_loc_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_install_guard, arc_2_0_install_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_code_guard, arc_2_0_code_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_data_guard, arc_2_0_data_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_ffi_guard, arc_2_0_ffi_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_share_guard, arc_2_0_share_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_must_guard, arc_2_0_must_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_loop_guard, arc_2_0_loop_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_seq_guard, arc_2_0_seq_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_if_guard, arc_2_0_if_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_tail_guard, arc_2_0_tail_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_callreturn_guard, arc_2_0_callreturn_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_0_callhandler_guard, arc_2_0_callhandler_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_skip_guard, arc_2_4_skip_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.skip : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_move_guard, arc_2_4_move_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_inst_guard, arc_2_4_inst_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_assign_guard, arc_2_4_assign_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_get_guard, arc_2_4_get_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_set_guard, arc_2_4_set_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_store_guard, arc_2_4_store_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_alloc_guard, arc_2_4_alloc_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_consts_guard, arc_2_4_consts_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_raise_guard, arc_2_4_raise_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.raise 99 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_return_guard, arc_2_4_return_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_break_guard, arc_2_4_break_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.break 777 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_continue_guard, arc_2_4_continue_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.continue 777 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_tick_guard, arc_2_4_tick_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.tick : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_heap_guard, arc_2_4_heap_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_loc_guard, arc_2_4_loc_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_install_guard, arc_2_4_install_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_code_guard, arc_2_4_code_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_data_guard, arc_2_4_data_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_ffi_guard, arc_2_4_ffi_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_share_guard, arc_2_4_share_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_must_guard, arc_2_4_must_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_loop_guard, arc_2_4_loop_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_seq_guard, arc_2_4_seq_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_if_guard, arc_2_4_if_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_tail_guard, arc_2_4_tail_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_callreturn_guard, arc_2_4_callreturn_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_2_4_callhandler_guard, arc_2_4_callhandler_result
example (conf : AsmConfigExact 2) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 2)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_skip_guard, arc_8_0_skip_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.skip : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_move_guard, arc_8_0_move_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_inst_guard, arc_8_0_inst_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_assign_guard, arc_8_0_assign_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_get_guard, arc_8_0_get_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_set_guard, arc_8_0_set_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_store_guard, arc_8_0_store_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_alloc_guard, arc_8_0_alloc_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_consts_guard, arc_8_0_consts_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_raise_guard, arc_8_0_raise_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.raise 99 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_return_guard, arc_8_0_return_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_break_guard, arc_8_0_break_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.break 777 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_continue_guard, arc_8_0_continue_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.continue 777 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_tick_guard, arc_8_0_tick_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.tick : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_heap_guard, arc_8_0_heap_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_loc_guard, arc_8_0_loc_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_install_guard, arc_8_0_install_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_code_guard, arc_8_0_code_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_data_guard, arc_8_0_data_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_ffi_guard, arc_8_0_ffi_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_share_guard, arc_8_0_share_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_must_guard, arc_8_0_must_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_loop_guard, arc_8_0_loop_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_seq_guard, arc_8_0_seq_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_if_guard, arc_8_0_if_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_tail_guard, arc_8_0_tail_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_callreturn_guard, arc_8_0_callreturn_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_0_callhandler_guard, arc_8_0_callhandler_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_skip_guard, arc_8_4_skip_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.skip : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_move_guard, arc_8_4_move_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_inst_guard, arc_8_4_inst_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_assign_guard, arc_8_4_assign_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_get_guard, arc_8_4_get_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_set_guard, arc_8_4_set_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_store_guard, arc_8_4_store_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_alloc_guard, arc_8_4_alloc_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_consts_guard, arc_8_4_consts_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_raise_guard, arc_8_4_raise_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.raise 99 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_return_guard, arc_8_4_return_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_break_guard, arc_8_4_break_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.break 777 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_continue_guard, arc_8_4_continue_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.continue 777 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_tick_guard, arc_8_4_tick_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.tick : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_heap_guard, arc_8_4_heap_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_loc_guard, arc_8_4_loc_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_install_guard, arc_8_4_install_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_code_guard, arc_8_4_code_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_data_guard, arc_8_4_data_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_ffi_guard, arc_8_4_ffi_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_share_guard, arc_8_4_share_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_must_guard, arc_8_4_must_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_loop_guard, arc_8_4_loop_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_seq_guard, arc_8_4_seq_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_if_guard, arc_8_4_if_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_tail_guard, arc_8_4_tail_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_callreturn_guard, arc_8_4_callreturn_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_8_4_callhandler_guard, arc_8_4_callhandler_result
example (conf : AsmConfigExact 8) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 8)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_skip_guard, arc_64_0_skip_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.skip : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_move_guard, arc_64_0_move_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_inst_guard, arc_64_0_inst_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_assign_guard, arc_64_0_assign_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_get_guard, arc_64_0_get_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_set_guard, arc_64_0_set_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_store_guard, arc_64_0_store_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_alloc_guard, arc_64_0_alloc_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_consts_guard, arc_64_0_consts_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_raise_guard, arc_64_0_raise_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.raise 99 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_return_guard, arc_64_0_return_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_break_guard, arc_64_0_break_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.break 777 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_continue_guard, arc_64_0_continue_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.continue 777 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_tick_guard, arc_64_0_tick_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.tick : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_heap_guard, arc_64_0_heap_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_loc_guard, arc_64_0_loc_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_install_guard, arc_64_0_install_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_code_guard, arc_64_0_code_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_data_guard, arc_64_0_data_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_ffi_guard, arc_64_0_ffi_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_share_guard, arc_64_0_share_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_must_guard, arc_64_0_must_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_loop_guard, arc_64_0_loop_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_seq_guard, arc_64_0_seq_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_if_guard, arc_64_0_if_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_tail_guard, arc_64_0_tail_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_callreturn_guard, arc_64_0_callreturn_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_0_callhandler_guard, arc_64_0_callhandler_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_skip_guard, arc_64_4_skip_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.skip : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_move_guard, arc_64_4_move_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_inst_guard, arc_64_4_inst_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_assign_guard, arc_64_4_assign_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_get_guard, arc_64_4_get_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_set_guard, arc_64_4_set_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_store_guard, arc_64_4_store_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_alloc_guard, arc_64_4_alloc_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_consts_guard, arc_64_4_consts_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_raise_guard, arc_64_4_raise_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.raise 99 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_return_guard, arc_64_4_return_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_break_guard, arc_64_4_break_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.break 777 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_continue_guard, arc_64_4_continue_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.continue 777 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_tick_guard, arc_64_4_tick_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.tick : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_heap_guard, arc_64_4_heap_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_loc_guard, arc_64_4_loc_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_install_guard, arc_64_4_install_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_code_guard, arc_64_4_code_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_data_guard, arc_64_4_data_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_ffi_guard, arc_64_4_ffi_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_share_guard, arc_64_4_share_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_must_guard, arc_64_4_must_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_loop_guard, arc_64_4_loop_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_seq_guard, arc_64_4_seq_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_if_guard, arc_64_4_if_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_tail_guard, arc_64_4_tail_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_callreturn_guard, arc_64_4_callreturn_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_64_4_callhandler_guard, arc_64_4_callhandler_result
example (conf : AsmConfigExact 64) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 64)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_skip_guard, arc_80_0_skip_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.skip : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_move_guard, arc_80_0_move_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_inst_guard, arc_80_0_inst_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_assign_guard, arc_80_0_assign_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_get_guard, arc_80_0_get_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_set_guard, arc_80_0_set_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_store_guard, arc_80_0_store_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_alloc_guard, arc_80_0_alloc_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_consts_guard, arc_80_0_consts_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_raise_guard, arc_80_0_raise_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.raise 99 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_return_guard, arc_80_0_return_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_break_guard, arc_80_0_break_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.break 777 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_continue_guard, arc_80_0_continue_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.continue 777 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_tick_guard, arc_80_0_tick_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.tick : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_heap_guard, arc_80_0_heap_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_loc_guard, arc_80_0_loc_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_install_guard, arc_80_0_install_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_code_guard, arc_80_0_code_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_data_guard, arc_80_0_data_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_ffi_guard, arc_80_0_ffi_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_share_guard, arc_80_0_share_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_must_guard, arc_80_0_must_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_loop_guard, arc_80_0_loop_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_seq_guard, arc_80_0_seq_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_if_guard, arc_80_0_if_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_tail_guard, arc_80_0_tail_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_callreturn_guard, arc_80_0_callreturn_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_0_callhandler_guard, arc_80_0_callhandler_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 4, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (0,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_skip_guard, arc_80_4_skip_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.skip : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_move_guard, arc_80_4_move_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_inst_guard, arc_80_4_inst_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_assign_guard, arc_80_4_assign_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_get_guard, arc_80_4_get_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_set_guard, arc_80_4_set_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_store_guard, arc_80_4_store_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_alloc_guard, arc_80_4_alloc_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_consts_guard, arc_80_4_consts_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_raise_guard, arc_80_4_raise_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.raise 99 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_return_guard, arc_80_4_return_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_break_guard, arc_80_4_break_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.break 777 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_continue_guard, arc_80_4_continue_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.continue 777 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_tick_guard, arc_80_4_tick_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.tick : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_heap_guard, arc_80_4_heap_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_loc_guard, arc_80_4_loc_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_install_guard, arc_80_4_install_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_code_guard, arc_80_4_code_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_data_guard, arc_80_4_data_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_ffi_guard, arc_80_4_ffi_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_share_guard, arc_80_4_share_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_must_guard, arc_80_4_must_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_loop_guard, arc_80_4_loop_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_seq_guard, arc_80_4_seq_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_if_guard, arc_80_4_if_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_tail_guard, arc_80_4_tail_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_callreturn_guard, arc_80_4_callreturn_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

-- arc_80_4_callhandler_guard, arc_80_4_callhandler_result
example (conf : AsmConfigExact 80) :
    stackAsmRemove {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]}
      (compNative {conf with regCount := 8, avoidRegs := [1180591620717411303424,1180591620717411303424]} false
        (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 80)) (.list [8,2],99) (4,1180591620717411303424,9)).1 := by
  apply wordToStackStackAsmRemove
  · cbv
  · rfl

example {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (p : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
    (room : 1 < conf.regCount - conf.avoidRegs.length) :
    stackAsmRemove conf (compNative conf false p bs (0,0,0)).1 := by
  exact wordToStackStackAsmRemove conf false p bs (0,0,0) room rfl

end Flapjack.Test.WordToStackAsmRemoveCompilerParity
