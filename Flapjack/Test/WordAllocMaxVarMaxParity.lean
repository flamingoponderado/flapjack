import Flapjack.Compiler.Backend.WordAlloc.Proofs.Maximum.MaxVar

namespace Flapjack.Test.WordAllocMaxVarMaxParity
open Compiler.Backend.WordAlloc

/-! Original full constructor observations from `word_alloc_max_var_max_probe.out`.
Every row compares actual maximum, occurrence at that maximum and strict-below
occurrence, then applies the unconditional theorem to the same native program. -/
private def observe {width : Nat} [NeZero width] (program : WordLangProgHOL (BitVec width)) :
    Nat × Bool × Bool :=
  (maxVarHOL program, everyVarHOL (fun x => decide (x ≤ maxVarHOL program)) program,
    everyVarHOL (fun x => decide (x < maxVarHOL program)) program)

private def mvm_skip : WordLangProgHOL (BitVec 64) :=
  .skip
example : observe mvm_skip = (0, true, true) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_skip)) mvm_skip = true :=
  maxVarMax mvm_skip

private def mvm_move : WordLangProgHOL (BitVec 64) :=
  .move 99 [(3,17),(23,5)]
example : observe mvm_move = (23, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_move)) mvm_move = true :=
  maxVarMax mvm_move

private def mvm_move_empty : WordLangProgHOL (BitVec 64) :=
  .move 99 []
example : observe mvm_move_empty = (0, true, true) := by decide +kernel
private def mvm_assign : WordLangProgHOL (BitVec 64) :=
  .assign 11 (.load (.var 17))
example : observe mvm_assign = (17, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_assign)) mvm_assign = true :=
  maxVarMax mvm_assign

private def mvm_get : WordLangProgHOL (BitVec 64) :=
  .get 7 .handler
example : observe mvm_get = (7, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_get)) mvm_get = true :=
  maxVarMax mvm_get

private def mvm_store : WordLangProgHOL (BitVec 64) :=
  .store (.shift .lsl (.var 5) (.var 17)) 3
example : observe mvm_store = (17, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_store)) mvm_store = true :=
  maxVarMax mvm_store

private def mvm_tail_ignored : WordLangProgHOL (BitVec 64) :=
  .call none (some 99) [5,17] (some (101,.raise 103,7,8))
example : observe mvm_tail_ignored = (17, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_tail_ignored)) mvm_tail_ignored = true :=
  maxVarMax mvm_tail_ignored

private def mvm_tail_empty : WordLangProgHOL (BitVec 64) :=
  .call none none [] (some (101,.raise 103,7,8))
example : observe mvm_tail_empty = (0, true, true) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_tail_empty)) mvm_tail_empty = true :=
  maxVarMax mvm_tail_empty

private def mvm_call_body : WordLangProgHOL (BitVec 64) :=
  .call (some ([5],(sptInsert 17 () .ln,.ln),.raise 23,7,8)) none [11] none
example : observe mvm_call_body = (23, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_call_body)) mvm_call_body = true :=
  maxVarMax mvm_call_body

private def mvm_call_cutset : WordLangProgHOL (BitVec 64) :=
  .call (some ([5],(.ln,sptInsert 47 () .ln),.raise 23,7,8)) none [11] none
example : observe mvm_call_cutset = (47, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_call_cutset)) mvm_call_cutset = true :=
  maxVarMax mvm_call_cutset

private def mvm_call_values : WordLangProgHOL (BitVec 64) :=
  .call (some ([53],(.ln,sptInsert 47 () .ln),.raise 23,7,8)) none [11] none
example : observe mvm_call_values = (53, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_call_values)) mvm_call_values = true :=
  maxVarMax mvm_call_values

private def mvm_handler_value : WordLangProgHOL (BitVec 64) :=
  .call (some ([5],(sptInsert 17 () .ln,.ln),.raise 23,7,8)) none [11] (some (37,.raise 29,9,10))
example : observe mvm_handler_value = (37, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_handler_value)) mvm_handler_value = true :=
  maxVarMax mvm_handler_value

private def mvm_handler_body : WordLangProgHOL (BitVec 64) :=
  .call (some ([5],(sptInsert 17 () .ln,.ln),.raise 23,7,8)) none [11] (some (37,.raise 61,9,10))
example : observe mvm_handler_body = (61, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_handler_body)) mvm_handler_body = true :=
  maxVarMax mvm_handler_body

private def mvm_seq : WordLangProgHOL (BitVec 64) :=
  .seq (.raise 5) (.raise 17)
example : observe mvm_seq = (17, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_seq)) mvm_seq = true :=
  maxVarMax mvm_seq

private def mvm_must : WordLangProgHOL (BitVec 64) :=
  .mustTerminate (.raise 17)
example : observe mvm_must = (17, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_must)) mvm_must = true :=
  maxVarMax mvm_must

private def mvm_if_reg : WordLangProgHOL (BitVec 64) :=
  .ite .equal 5 (.reg 23) (.raise 17) (.raise 11)
example : observe mvm_if_reg = (23, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_if_reg)) mvm_if_reg = true :=
  maxVarMax mvm_if_reg

private def mvm_if_imm : WordLangProgHOL (BitVec 64) :=
  .ite .equal 5 (.imm 99) (.raise 17) (.raise 11)
example : observe mvm_if_imm = (17, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_if_imm)) mvm_if_imm = true :=
  maxVarMax mvm_if_imm

private def mvm_alloc : WordLangProgHOL (BitVec 64) :=
  .alloc 7 (sptInsert 17 () .ln,sptInsert 23 () .ln)
example : observe mvm_alloc = (23, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_alloc)) mvm_alloc = true :=
  maxVarMax mvm_alloc

private def mvm_consts : WordLangProgHOL (BitVec 64) :=
  .storeConsts 3 17 23 5 [(true,99)]
example : observe mvm_consts = (23, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_consts)) mvm_consts = true :=
  maxVarMax mvm_consts

private def mvm_install : WordLangProgHOL (BitVec 64) :=
  .install 3 5 7 11 (.ln,sptInsert 23 () .ln)
example : observe mvm_install = (23, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_install)) mvm_install = true :=
  maxVarMax mvm_install

private def mvm_codewrite : WordLangProgHOL (BitVec 64) :=
  .codeBufferWrite 3 17
example : observe mvm_codewrite = (17, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_codewrite)) mvm_codewrite = true :=
  maxVarMax mvm_codewrite

private def mvm_datawrite : WordLangProgHOL (BitVec 64) :=
  .dataBufferWrite 23 5
example : observe mvm_datawrite = (23, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_datawrite)) mvm_datawrite = true :=
  maxVarMax mvm_datawrite

private def mvm_ffi : WordLangProgHOL (BitVec 64) :=
  .ffi (.implode [120]) 3 5 7 11 (sptInsert 17 () .ln,sptInsert 23 () .ln)
example : observe mvm_ffi = (23, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_ffi)) mvm_ffi = true :=
  maxVarMax mvm_ffi

private def mvm_raise : WordLangProgHOL (BitVec 64) :=
  .raise 17
example : observe mvm_raise = (17, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_raise)) mvm_raise = true :=
  maxVarMax mvm_raise

private def mvm_heap : WordLangProgHOL (BitVec 64) :=
  .opCurrHeap .add 3 17
example : observe mvm_heap = (17, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_heap)) mvm_heap = true :=
  maxVarMax mvm_heap

private def mvm_return : WordLangProgHOL (BitVec 64) :=
  .return 3 [5,17]
example : observe mvm_return = (17, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_return)) mvm_return = true :=
  maxVarMax mvm_return

private def mvm_return_empty : WordLangProgHOL (BitVec 64) :=
  .return 0 []
example : observe mvm_return_empty = (0, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_return_empty)) mvm_return_empty = true :=
  maxVarMax mvm_return_empty

private def mvm_tick : WordLangProgHOL (BitVec 64) :=
  .tick
example : observe mvm_tick = (0, true, true) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_tick)) mvm_tick = true :=
  maxVarMax mvm_tick

private def mvm_loc : WordLangProgHOL (BitVec 64) :=
  .locValue 7 99
example : observe mvm_loc = (7, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_loc)) mvm_loc = true :=
  maxVarMax mvm_loc

private def mvm_set : WordLangProgHOL (BitVec 64) :=
  .set .currHeap (.load (.var 17))
example : observe mvm_set = (17, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_set)) mvm_set = true :=
  maxVarMax mvm_set

private def mvm_share : WordLangProgHOL (BitVec 64) :=
  .shareInst .load8 3 (.op .add [.var 5,.const 99])
example : observe mvm_share = (5, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_share)) mvm_share = true :=
  maxVarMax mvm_share

private def mvm_loop_exit : WordLangProgHOL (BitVec 64) :=
  .loop (sptInsert 17 () .ln) (.raise 23) (sptInsert 29 () .ln)
example : observe mvm_loop_exit = (29, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_loop_exit)) mvm_loop_exit = true :=
  maxVarMax mvm_loop_exit

private def mvm_loop_body : WordLangProgHOL (BitVec 64) :=
  .loop (sptInsert 17 () .ln) (.raise 31) (sptInsert 29 () .ln)
example : observe mvm_loop_body = (31, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_loop_body)) mvm_loop_body = true :=
  maxVarMax mvm_loop_body

private def mvm_break : WordLangProgHOL (BitVec 64) :=
  .break 99
example : observe mvm_break = (0, true, true) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_break)) mvm_break = true :=
  maxVarMax mvm_break

private def mvm_continue : WordLangProgHOL (BitVec 64) :=
  .continue 99
example : observe mvm_continue = (0, true, true) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_continue)) mvm_continue = true :=
  maxVarMax mvm_continue

private def mvm_width1_huge : WordLangProgHOL (BitVec 1) :=
  .assign 1208925819614629174706176 (.var 7)
example : observe mvm_width1_huge = (1208925819614629174706176, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_width1_huge)) mvm_width1_huge = true :=
  maxVarMax mvm_width1_huge

private def mvm_inst_load16_ignored : WordLangProgHOL (BitVec 64) :=
  .inst (.mem .load16 999 (.addr 777 3))
example : observe mvm_inst_load16_ignored = (0, true, true) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_inst_load16_ignored)) mvm_inst_load16_ignored = true :=
  maxVarMax mvm_inst_load16_ignored

private def mvm_inst_store16_ignored : WordLangProgHOL (BitVec 64) :=
  .inst (.mem .store16 999 (.addr 777 3))
example : observe mvm_inst_store16_ignored = (0, true, true) := by decide +kernel
private def mvm_call_arguments : WordLangProgHOL (BitVec 64) :=
  .call (some ([5],(.ln,.ln),.raise 3,999,999)) none [97] none
example : observe mvm_call_arguments = (97, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_call_arguments)) mvm_call_arguments = true :=
  maxVarMax mvm_call_arguments

private def mvm_call_nested_handler : WordLangProgHOL (BitVec 32) :=
  .call (some ([5],(.ln,.ln),.raise 3,999,999)) none [7] (some (11,.loop .ln (.return 13 [17]) .ln,999,999))
example : observe mvm_call_nested_handler = (17, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_call_nested_handler)) mvm_call_nested_handler = true :=
  maxVarMax mvm_call_nested_handler

private def mvm_cutsets_nonwf : WordLangProgHOL (BitVec 64) :=
  .alloc 0 (.bn .ln .ln,.bs .ln () .ln)
example : observe mvm_cutsets_nonwf = (0, true, false) := by decide +kernel
example : everyVarHOL (fun x => decide (x ≤ maxVarHOL mvm_cutsets_nonwf)) mvm_cutsets_nonwf = true :=
  maxVarMax mvm_cutsets_nonwf

private def mvm_op_list_nested : WordLangProgHOL (BitVec 80) :=
  .set .currHeap (.op .add [.var 3,.load (.var 101),.op .sub [.var 17,.const 3]])
example : observe mvm_op_list_nested = (101, true, false) := by decide +kernel
example {width : Nat} [NeZero width] (program : WordLangProgHOL (BitVec width)) :
    everyVarHOL (fun x => decide (x ≤ maxVarHOL program)) program = true :=
  maxVarMax program

end Flapjack.Test.WordAllocMaxVarMaxParity
