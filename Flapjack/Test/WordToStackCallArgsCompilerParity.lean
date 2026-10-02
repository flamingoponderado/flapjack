import Flapjack.Compiler.Backend.WordToStack.Proofs.CallArgsCompiler

namespace Flapjack.Test.WordToStackCallArgsCompilerParity
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm
open Flapjack.WordToStackProofs.CallArgsCompiler
/- Original boundary: direct post-allocation guard EVAL and full original theorem
applications at the same nested program inputs; no direct target EVAL claim. -/

-- cca_1_skip_guard / cca_1_skip_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false .skip
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_move_guard / cca_1_move_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.move 0 [(2,4),(4,2)])
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_inst_guard / cca_1_inst_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.inst (.const 2 7))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_assign_guard / cca_1_assign_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.assign 2 (.const 7))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_get_guard / cca_1_get_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.get 2 .currHeap)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_set_guard / cca_1_set_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.set .handler (.var 2))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_store_guard / cca_1_store_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.store (.var 2) 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_must_guard / cca_1_must_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln)))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_tail_guard / cca_1_tail_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.call none none [0,2,4] (some (999,.install 999 999 999 999 (.ln,.ln),7,8)))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_ret_guard / cca_1_ret_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.call (some ([2,4],(.ln,.ln),.alloc 2 (.ln,.ln),7,8)) (some 17) [2,4] none)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_handler_guard / cca_1_handler_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.call (some ([],(.ln,.ln),.mustTerminate .tick,7,8)) none [] (some (2,.alloc 2 (.ln,.ln),9,10)))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_seq_guard / cca_1_seq_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.mustTerminate .tick))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_if_guard / cca_1_if_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.mustTerminate .tick))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_loop_guard / cca_1_loop_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_alloc_guard / cca_1_alloc_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.alloc 2 (.ln,.ln))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_consts_guard / cca_1_consts_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.storeConsts 0 2 4 6 [(true,7)])
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_raise_guard / cca_1_raise_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.raise 2)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_return_guard / cca_1_return_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.return 2 [2,4])
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_break_guard / cca_1_break_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.break 17)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_continue_guard / cca_1_continue_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.continue 17)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_tick_guard / cca_1_tick_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false .tick
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_heap_guard / cca_1_heap_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.opCurrHeap .add 2 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_loc_guard / cca_1_loc_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.locValue 2 17)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_install_guard / cca_1_install_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.install 2 4 6 8 (.ln,.ln))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_code_guard / cca_1_code_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.codeBufferWrite 2 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_data_guard / cca_1_data_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.dataBufferWrite 2 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_ffi_guard / cca_1_ffi_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_1_share_guard / cca_1_share_target
example (conf : AsmConfigExact 1) : callArgs (compNative conf false (.shareInst .load 2 (.var 4))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_skip_guard / cca_2_skip_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false .skip
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_move_guard / cca_2_move_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.move 0 [(2,4),(4,2)])
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_inst_guard / cca_2_inst_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.inst (.const 2 7))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_assign_guard / cca_2_assign_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.assign 2 (.const 7))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_get_guard / cca_2_get_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.get 2 .currHeap)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_set_guard / cca_2_set_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.set .handler (.var 2))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_store_guard / cca_2_store_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.store (.var 2) 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_must_guard / cca_2_must_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln)))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_tail_guard / cca_2_tail_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.call none none [0,2,4] (some (999,.install 999 999 999 999 (.ln,.ln),7,8)))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_ret_guard / cca_2_ret_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.call (some ([2,4],(.ln,.ln),.alloc 2 (.ln,.ln),7,8)) (some 17) [2,4] none)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_handler_guard / cca_2_handler_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.call (some ([],(.ln,.ln),.mustTerminate .tick,7,8)) none [] (some (2,.alloc 2 (.ln,.ln),9,10)))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_seq_guard / cca_2_seq_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.mustTerminate .tick))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_if_guard / cca_2_if_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.mustTerminate .tick))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_loop_guard / cca_2_loop_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_alloc_guard / cca_2_alloc_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.alloc 2 (.ln,.ln))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_consts_guard / cca_2_consts_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.storeConsts 0 2 4 6 [(true,7)])
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_raise_guard / cca_2_raise_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.raise 2)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_return_guard / cca_2_return_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.return 2 [2,4])
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_break_guard / cca_2_break_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.break 17)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_continue_guard / cca_2_continue_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.continue 17)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_tick_guard / cca_2_tick_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false .tick
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_heap_guard / cca_2_heap_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.opCurrHeap .add 2 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_loc_guard / cca_2_loc_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.locValue 2 17)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_install_guard / cca_2_install_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.install 2 4 6 8 (.ln,.ln))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_code_guard / cca_2_code_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.codeBufferWrite 2 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_data_guard / cca_2_data_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.dataBufferWrite 2 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_ffi_guard / cca_2_ffi_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_2_share_guard / cca_2_share_target
example (conf : AsmConfigExact 2) : callArgs (compNative conf false (.shareInst .load 2 (.var 4))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_skip_guard / cca_8_skip_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false .skip
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_move_guard / cca_8_move_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.move 0 [(2,4),(4,2)])
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_inst_guard / cca_8_inst_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.inst (.const 2 7))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_assign_guard / cca_8_assign_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.assign 2 (.const 7))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_get_guard / cca_8_get_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.get 2 .currHeap)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_set_guard / cca_8_set_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.set .handler (.var 2))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_store_guard / cca_8_store_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.store (.var 2) 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_must_guard / cca_8_must_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln)))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_tail_guard / cca_8_tail_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.call none none [0,2,4] (some (999,.install 999 999 999 999 (.ln,.ln),7,8)))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_ret_guard / cca_8_ret_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.call (some ([2,4],(.ln,.ln),.alloc 2 (.ln,.ln),7,8)) (some 17) [2,4] none)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_handler_guard / cca_8_handler_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.call (some ([],(.ln,.ln),.mustTerminate .tick,7,8)) none [] (some (2,.alloc 2 (.ln,.ln),9,10)))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_seq_guard / cca_8_seq_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.mustTerminate .tick))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_if_guard / cca_8_if_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.mustTerminate .tick))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_loop_guard / cca_8_loop_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_alloc_guard / cca_8_alloc_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.alloc 2 (.ln,.ln))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_consts_guard / cca_8_consts_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.storeConsts 0 2 4 6 [(true,7)])
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_raise_guard / cca_8_raise_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.raise 2)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_return_guard / cca_8_return_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.return 2 [2,4])
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_break_guard / cca_8_break_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.break 17)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_continue_guard / cca_8_continue_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.continue 17)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_tick_guard / cca_8_tick_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false .tick
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_heap_guard / cca_8_heap_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.opCurrHeap .add 2 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_loc_guard / cca_8_loc_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.locValue 2 17)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_install_guard / cca_8_install_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.install 2 4 6 8 (.ln,.ln))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_code_guard / cca_8_code_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.codeBufferWrite 2 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_data_guard / cca_8_data_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.dataBufferWrite 2 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_ffi_guard / cca_8_ffi_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_8_share_guard / cca_8_share_target
example (conf : AsmConfigExact 8) : callArgs (compNative conf false (.shareInst .load 2 (.var 4))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_skip_guard / cca_64_skip_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false .skip
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_move_guard / cca_64_move_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.move 0 [(2,4),(4,2)])
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_inst_guard / cca_64_inst_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.inst (.const 2 7))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_assign_guard / cca_64_assign_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.assign 2 (.const 7))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_get_guard / cca_64_get_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.get 2 .currHeap)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_set_guard / cca_64_set_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.set .handler (.var 2))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_store_guard / cca_64_store_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.store (.var 2) 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_must_guard / cca_64_must_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln)))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_tail_guard / cca_64_tail_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.call none none [0,2,4] (some (999,.install 999 999 999 999 (.ln,.ln),7,8)))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_ret_guard / cca_64_ret_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.call (some ([2,4],(.ln,.ln),.alloc 2 (.ln,.ln),7,8)) (some 17) [2,4] none)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_handler_guard / cca_64_handler_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.call (some ([],(.ln,.ln),.mustTerminate .tick,7,8)) none [] (some (2,.alloc 2 (.ln,.ln),9,10)))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_seq_guard / cca_64_seq_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.mustTerminate .tick))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_if_guard / cca_64_if_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.mustTerminate .tick))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_loop_guard / cca_64_loop_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_alloc_guard / cca_64_alloc_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.alloc 2 (.ln,.ln))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_consts_guard / cca_64_consts_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.storeConsts 0 2 4 6 [(true,7)])
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_raise_guard / cca_64_raise_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.raise 2)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_return_guard / cca_64_return_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.return 2 [2,4])
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_break_guard / cca_64_break_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.break 17)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_continue_guard / cca_64_continue_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.continue 17)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_tick_guard / cca_64_tick_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false .tick
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_heap_guard / cca_64_heap_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.opCurrHeap .add 2 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_loc_guard / cca_64_loc_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.locValue 2 17)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_install_guard / cca_64_install_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.install 2 4 6 8 (.ln,.ln))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_code_guard / cca_64_code_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.codeBufferWrite 2 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_data_guard / cca_64_data_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.dataBufferWrite 2 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_ffi_guard / cca_64_ffi_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_64_share_guard / cca_64_share_target
example (conf : AsmConfigExact 64) : callArgs (compNative conf false (.shareInst .load 2 (.var 4))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_skip_guard / cca_80_skip_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false .skip
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_move_guard / cca_80_move_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.move 0 [(2,4),(4,2)])
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_inst_guard / cca_80_inst_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.inst (.const 2 7))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_assign_guard / cca_80_assign_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.assign 2 (.const 7))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_get_guard / cca_80_get_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.get 2 .currHeap)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_set_guard / cca_80_set_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.set .handler (.var 2))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_store_guard / cca_80_store_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.store (.var 2) 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_must_guard / cca_80_must_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.mustTerminate (.alloc 2 (.ln,.ln)))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_tail_guard / cca_80_tail_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.call none none [0,2,4] (some (999,.install 999 999 999 999 (.ln,.ln),7,8)))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_ret_guard / cca_80_ret_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.call (some ([2,4],(.ln,.ln),.alloc 2 (.ln,.ln),7,8)) (some 17) [2,4] none)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_handler_guard / cca_80_handler_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.call (some ([],(.ln,.ln),.mustTerminate .tick,7,8)) none [] (some (2,.alloc 2 (.ln,.ln),9,10)))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_seq_guard / cca_80_seq_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.seq (.alloc 2 (.ln,.ln)) (.mustTerminate .tick))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_if_guard / cca_80_if_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.ite .equal 2 (.imm 7) (.alloc 2 (.ln,.ln)) (.mustTerminate .tick))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_loop_guard / cca_80_loop_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.loop .ln (.alloc 2 (.ln,.ln)) .ln)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_alloc_guard / cca_80_alloc_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.alloc 2 (.ln,.ln))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_consts_guard / cca_80_consts_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.storeConsts 0 2 4 6 [(true,7)])
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_raise_guard / cca_80_raise_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.raise 2)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_return_guard / cca_80_return_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.return 2 [2,4])
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_break_guard / cca_80_break_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.break 17)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_continue_guard / cca_80_continue_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.continue 17)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_tick_guard / cca_80_tick_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false .tick
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_heap_guard / cca_80_heap_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.opCurrHeap .add 2 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_loc_guard / cca_80_loc_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.locValue 2 17)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_install_guard / cca_80_install_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.install 2 4 6 8 (.ln,.ln))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_code_guard / cca_80_code_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.codeBufferWrite 2 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_data_guard / cca_80_data_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.dataBufferWrite 2 4)
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_ffi_guard / cca_80_ffi_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

-- cca_80_share_guard / cca_80_share_target
example (conf : AsmConfigExact 80) : callArgs (compNative conf false (.shareInst .load 2 (.var 4))
    (.append (.list [4]) (.list [7]),17) (4,7,9)).1 1 2 3 4 0 := by
  apply wordToStackCallArgs conf false _ _ _ _ rfl
  cbv

#print axioms Flapjack.WordToStackProofs.CallArgsCompiler.wordToStackCallArgs
end Flapjack.Test.WordToStackCallArgsCompilerParity
