import Flapjack.Pancake.WordLang.MaxVar

namespace Flapjack.Test.WordLangMaxVarParity
open Flapjack

-- Kernel replays of freshly captured original HOL rows.
-- mv_skip
example : maxVarHOL (width := 64) (.skip) = 0 := by cbv

-- mv_move
example : maxVarHOL (width := 64) (.move 99 [(3,17),(23,5)]) = 23 := by cbv

-- mv_move_empty
example : maxVarHOL (width := 64) (.move 99 []) = 0 := by cbv

-- mv_inst64
example : maxVarHOL (width := 64) (.inst (.fp (.fpMovToReg 3 17 99))) = 3 := by cbv

-- mv_inst32
example : maxVarHOL (width := 32) (.inst (.fp (.fpMovToReg 3 17 99))) = 17 := by cbv

-- mv_assign
example : maxVarHOL (width := 64) (.assign 11 (.load (.var 17))) = 17 := by cbv

-- mv_get
example : maxVarHOL (width := 64) (.get 7 .handler) = 7 := by cbv

-- mv_store
example : maxVarHOL (width := 64) (.store (.shift .lsl (.var 5) (.var 17)) 3) = 17 := by cbv

-- mv_tail_ignored
example : maxVarHOL (width := 64) (.call none (some 99) [5,17] (some (101,.raise 103,7,8))) = 17 := by cbv

-- mv_tail_empty
example : maxVarHOL (width := 64) (.call none none [] (some (101,.raise 103,7,8))) = 0 := by cbv

-- mv_call_body
example : maxVarHOL (width := 64) (.call (some ([5],(sptInsert 17 () .ln,.ln),.raise 23,7,8)) none [11] none) = 23 := by cbv

-- mv_call_cutset
example : maxVarHOL (width := 64) (.call (some ([5],(.ln,sptInsert 47 () .ln),.raise 23,7,8)) none [11] none) = 47 := by cbv

-- mv_call_values
example : maxVarHOL (width := 64) (.call (some ([53],(.ln,sptInsert 47 () .ln),.raise 23,7,8)) none [11] none) = 53 := by cbv

-- mv_handler_value
example : maxVarHOL (width := 64) (.call (some ([5],(sptInsert 17 () .ln,.ln),.raise 23,7,8)) none [11] (some (37,.raise 29,9,10))) = 37 := by cbv

-- mv_handler_body
example : maxVarHOL (width := 64) (.call (some ([5],(sptInsert 17 () .ln,.ln),.raise 23,7,8)) none [11] (some (37,.raise 61,9,10))) = 61 := by cbv

-- mv_seq
example : maxVarHOL (width := 64) (.seq (.raise 5) (.raise 17)) = 17 := by cbv

-- mv_must
example : maxVarHOL (width := 64) (.mustTerminate (.raise 17)) = 17 := by cbv

-- mv_if_reg
example : maxVarHOL (width := 64) (.ite .equal 5 (.reg 23) (.raise 17) (.raise 11)) = 23 := by cbv

-- mv_if_imm
example : maxVarHOL (width := 64) (.ite .equal 5 (.imm 99) (.raise 17) (.raise 11)) = 17 := by cbv

-- mv_alloc
example : maxVarHOL (width := 64) (.alloc 7 (sptInsert 17 () .ln,sptInsert 23 () .ln)) = 23 := by cbv

-- mv_consts
example : maxVarHOL (width := 64) (.storeConsts 3 17 23 5 [(true,99)]) = 23 := by cbv

-- mv_install
example : maxVarHOL (width := 64) (.install 3 5 7 11 (.ln,sptInsert 23 () .ln)) = 23 := by cbv

-- mv_codewrite
example : maxVarHOL (width := 64) (.codeBufferWrite 3 17) = 17 := by cbv

-- mv_datawrite
example : maxVarHOL (width := 64) (.dataBufferWrite 23 5) = 23 := by cbv

-- mv_ffi
example : maxVarHOL (width := 64) (.ffi (.implode [120]) 3 5 7 11 (sptInsert 17 () .ln,sptInsert 23 () .ln)) = 23 := by cbv

-- mv_raise
example : maxVarHOL (width := 64) (.raise 17) = 17 := by cbv

-- mv_heap
example : maxVarHOL (width := 64) (.opCurrHeap .add 3 17) = 17 := by cbv

-- mv_return
example : maxVarHOL (width := 64) (.return 3 [5,17]) = 17 := by cbv

-- mv_return_empty
example : maxVarHOL (width := 64) (.return 0 []) = 0 := by cbv

-- mv_tick
example : maxVarHOL (width := 64) (.tick) = 0 := by cbv

-- mv_loc
example : maxVarHOL (width := 64) (.locValue 7 99) = 7 := by cbv

-- mv_set
example : maxVarHOL (width := 64) (.set .currHeap (.load (.var 17))) = 17 := by cbv

-- mv_share
example : maxVarHOL (width := 64) (.shareInst .load8 3 (.op .add [.var 5,.const 99])) = 5 := by cbv

-- mv_loop_exit
example : maxVarHOL (width := 64) (.loop (sptInsert 17 () .ln) (.raise 23) (sptInsert 29 () .ln)) = 29 := by cbv

-- mv_loop_body
example : maxVarHOL (width := 64) (.loop (sptInsert 17 () .ln) (.raise 31) (sptInsert 29 () .ln)) = 31 := by cbv

-- mv_break
example : maxVarHOL (width := 64) (.break 99) = 0 := by cbv

-- mv_continue
example : maxVarHOL (width := 64) (.continue 99) = 0 := by cbv

end Flapjack.Test.WordLangMaxVarParity
