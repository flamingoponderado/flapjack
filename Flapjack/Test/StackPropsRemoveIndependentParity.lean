import Flapjack.Compiler.Backend.StackProps.RemoveNames

namespace Flapjack.Test.StackPropsRemoveIndependentParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm
/- Fresh original predicates at independent configuration/program dimensions.
Expected truth values come from stack_props_remove_independent_probe.out;
all34program constructor families and natural-subtraction underflow are covered.
The original same-width captured output is unchanged. -/

example {configWidth width : Nat} [NeZero configWidth] [NeZero width]
    (conf : AsmConfigExact configWidth) (p : HolProg width) :
    stackAsmRemove conf (.seq p .skip) ↔ stackAsmRemove conf p := by
  simp [stackAsmRemove]

-- asrc_1_80_0_get_last=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.get 5 .currHeap) : HolProg 80) := by cbv

-- asrc_1_80_0_get_bound=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.get 6 .currHeap) : HolProg 80) := by cbv

-- asrc_1_80_0_set=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.set .currHeap 1) : HolProg 80) := by cbv

-- asrc_1_80_0_store_ignored_second=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStore 1 99) : HolProg 80) := by cbv

-- asrc_1_80_0_store_first_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStore 6 1) : HolProg 80) := by cbv

-- asrc_1_80_0_load_ignored_second=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoad 1 99) : HolProg 80) := by cbv

-- asrc_1_80_0_load_first_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoad 6 1) : HolProg 80) := by cbv

-- asrc_1_80_0_get_size=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackGetSize 1) : HolProg 80) := by cbv

-- asrc_1_80_0_set_size_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackSetSize 6) : HolProg 80) := by cbv

-- asrc_1_80_0_heap=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.opCurrHeap .add 1 2) : HolProg 80) := by cbv

-- asrc_1_80_0_store_any_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStoreAny 1 6) : HolProg 80) := by cbv

-- asrc_1_80_0_load_any=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoadAny 1 2) : HolProg 80) := by cbv

-- asrc_1_80_0_bitmap_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.bitmapLoad 6 1) : HolProg 80) := by cbv

-- asrc_1_80_0_consts=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.storeConsts 1 2 (some 99)) : HolProg 80) := by cbv

-- asrc_1_80_0_seq_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.seq (.get 1 .currHeap) (.get 6 .currHeap)) : HolProg 80) := by cbv

-- asrc_1_80_0_if_ignored_condition=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.ite .equal 99 (.reg 99) .skip .skip) : HolProg 80) := by cbv

-- asrc_1_80_0_loop_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.loop (.get 6 .currHeap)) : HolProg 80) := by cbv

-- asrc_1_80_0_call_none_ignored=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call none (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 80) := by cbv

-- asrc_1_80_0_call_body_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.get 6 .currHeap,99,1,2)) (.inr 99) none) : HolProg 80) := by cbv

-- asrc_1_80_0_call_handler_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.skip,99,1,2)) (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 80) := by cbv

-- asrc_1_80_0_call_both_good=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.get 1 .currHeap,99,1,2)) (.inr 99) (some (.get 2 .currHeap,3,4))) : HolProg 80) := by cbv

-- asrc_1_80_0_inst_ignored=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.inst (.const 99 0)) : HolProg 80) := by cbv

-- asrc_1_80_0_skip=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 80) := by cbv

-- asrc_1_80_0_jump=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.jumpLower 900 901 902 : HolProg 80) := by cbv

-- asrc_1_80_0_alloc=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.alloc 900 : HolProg 80) := by cbv

-- asrc_1_80_0_raise=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.raise 900 : HolProg 80) := by cbv

-- asrc_1_80_0_ret=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.ret 900 : HolProg 80) := by cbv

-- asrc_1_80_0_break=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.break 900 : HolProg 80) := by cbv

-- asrc_1_80_0_continue=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.continue 900 : HolProg 80) := by cbv

-- asrc_1_80_0_ffi=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.ffi (Basis.Pure.MlString.ofString "abc") 900 901 902 903 904 : HolProg 80) := by cbv

-- asrc_1_80_0_tick=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.tick : HolProg 80) := by cbv

-- asrc_1_80_0_loc=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.locValue 900 901 902 : HolProg 80) := by cbv

-- asrc_1_80_0_install=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.install 900 901 902 903 904 : HolProg 80) := by cbv

-- asrc_1_80_0_share=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.shMemOp .load 900 (.addr 901 0) : HolProg 80) := by cbv

-- asrc_1_80_0_code=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.codeBufferWrite 900 901 : HolProg 80) := by cbv

-- asrc_1_80_0_data=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.dataBufferWrite 900 901 : HolProg 80) := by cbv

-- asrc_1_80_0_raw=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.rawCall 900 : HolProg 80) := by cbv

-- asrc_1_80_0_stackalloc=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.stackAlloc 900 : HolProg 80) := by cbv

-- asrc_1_80_0_stackfree=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.stackFree 900 : HolProg 80) := by cbv

-- asrc_1_80_0_halt=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.halt 900 : HolProg 80) := by cbv

-- asrc_1_80_1_get_last=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.get 5 .currHeap) : HolProg 80) := by cbv

-- asrc_1_80_1_get_bound=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.get 6 .currHeap) : HolProg 80) := by cbv

-- asrc_1_80_1_set=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.set .currHeap 1) : HolProg 80) := by cbv

-- asrc_1_80_1_store_ignored_second=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackStore 1 99) : HolProg 80) := by cbv

-- asrc_1_80_1_store_first_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackStore 6 1) : HolProg 80) := by cbv

-- asrc_1_80_1_load_ignored_second=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackLoad 1 99) : HolProg 80) := by cbv

-- asrc_1_80_1_load_first_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackLoad 6 1) : HolProg 80) := by cbv

-- asrc_1_80_1_get_size=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackGetSize 1) : HolProg 80) := by cbv

-- asrc_1_80_1_set_size_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackSetSize 6) : HolProg 80) := by cbv

-- asrc_1_80_1_heap=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.opCurrHeap .add 1 2) : HolProg 80) := by cbv

-- asrc_1_80_1_store_any_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackStoreAny 1 6) : HolProg 80) := by cbv

-- asrc_1_80_1_load_any=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackLoadAny 1 2) : HolProg 80) := by cbv

-- asrc_1_80_1_bitmap_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.bitmapLoad 6 1) : HolProg 80) := by cbv

-- asrc_1_80_1_consts=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.storeConsts 1 2 (some 99)) : HolProg 80) := by cbv

-- asrc_1_80_1_seq_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.seq (.get 1 .currHeap) (.get 6 .currHeap)) : HolProg 80) := by cbv

-- asrc_1_80_1_if_ignored_condition=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.ite .equal 99 (.reg 99) .skip .skip) : HolProg 80) := by cbv

-- asrc_1_80_1_loop_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.loop (.get 6 .currHeap)) : HolProg 80) := by cbv

-- asrc_1_80_1_call_none_ignored=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call none (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 80) := by cbv

-- asrc_1_80_1_call_body_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call (some (.get 6 .currHeap,99,1,2)) (.inr 99) none) : HolProg 80) := by cbv

-- asrc_1_80_1_call_handler_bad=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call (some (.skip,99,1,2)) (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 80) := by cbv

-- asrc_1_80_1_call_both_good=F
example (c : AsmConfigExact 1) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call (some (.get 1 .currHeap,99,1,2)) (.inr 99) (some (.get 2 .currHeap,3,4))) : HolProg 80) := by cbv

-- asrc_1_80_1_inst_ignored=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.inst (.const 99 0)) : HolProg 80) := by cbv

-- asrc_1_80_1_skip=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.skip : HolProg 80) := by cbv

-- asrc_1_80_1_jump=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.jumpLower 900 901 902 : HolProg 80) := by cbv

-- asrc_1_80_1_alloc=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.alloc 900 : HolProg 80) := by cbv

-- asrc_1_80_1_raise=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.raise 900 : HolProg 80) := by cbv

-- asrc_1_80_1_ret=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.ret 900 : HolProg 80) := by cbv

-- asrc_1_80_1_break=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.break 900 : HolProg 80) := by cbv

-- asrc_1_80_1_continue=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.continue 900 : HolProg 80) := by cbv

-- asrc_1_80_1_ffi=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.ffi (Basis.Pure.MlString.ofString "abc") 900 901 902 903 904 : HolProg 80) := by cbv

-- asrc_1_80_1_tick=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.tick : HolProg 80) := by cbv

-- asrc_1_80_1_loc=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.locValue 900 901 902 : HolProg 80) := by cbv

-- asrc_1_80_1_install=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.install 900 901 902 903 904 : HolProg 80) := by cbv

-- asrc_1_80_1_share=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.shMemOp .load 900 (.addr 901 0) : HolProg 80) := by cbv

-- asrc_1_80_1_code=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.codeBufferWrite 900 901 : HolProg 80) := by cbv

-- asrc_1_80_1_data=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.dataBufferWrite 900 901 : HolProg 80) := by cbv

-- asrc_1_80_1_raw=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.rawCall 900 : HolProg 80) := by cbv

-- asrc_1_80_1_stackalloc=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.stackAlloc 900 : HolProg 80) := by cbv

-- asrc_1_80_1_stackfree=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.stackFree 900 : HolProg 80) := by cbv

-- asrc_1_80_1_halt=T
example (c : AsmConfigExact 1) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.halt 900 : HolProg 80) := by cbv

-- asrc_80_1_0_get_last=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.get 5 .currHeap) : HolProg 1) := by cbv

-- asrc_80_1_0_get_bound=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.get 6 .currHeap) : HolProg 1) := by cbv

-- asrc_80_1_0_set=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.set .currHeap 1) : HolProg 1) := by cbv

-- asrc_80_1_0_store_ignored_second=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStore 1 99) : HolProg 1) := by cbv

-- asrc_80_1_0_store_first_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStore 6 1) : HolProg 1) := by cbv

-- asrc_80_1_0_load_ignored_second=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoad 1 99) : HolProg 1) := by cbv

-- asrc_80_1_0_load_first_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoad 6 1) : HolProg 1) := by cbv

-- asrc_80_1_0_get_size=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackGetSize 1) : HolProg 1) := by cbv

-- asrc_80_1_0_set_size_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackSetSize 6) : HolProg 1) := by cbv

-- asrc_80_1_0_heap=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.opCurrHeap .add 1 2) : HolProg 1) := by cbv

-- asrc_80_1_0_store_any_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStoreAny 1 6) : HolProg 1) := by cbv

-- asrc_80_1_0_load_any=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoadAny 1 2) : HolProg 1) := by cbv

-- asrc_80_1_0_bitmap_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.bitmapLoad 6 1) : HolProg 1) := by cbv

-- asrc_80_1_0_consts=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.storeConsts 1 2 (some 99)) : HolProg 1) := by cbv

-- asrc_80_1_0_seq_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.seq (.get 1 .currHeap) (.get 6 .currHeap)) : HolProg 1) := by cbv

-- asrc_80_1_0_if_ignored_condition=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.ite .equal 99 (.reg 99) .skip .skip) : HolProg 1) := by cbv

-- asrc_80_1_0_loop_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.loop (.get 6 .currHeap)) : HolProg 1) := by cbv

-- asrc_80_1_0_call_none_ignored=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call none (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 1) := by cbv

-- asrc_80_1_0_call_body_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.get 6 .currHeap,99,1,2)) (.inr 99) none) : HolProg 1) := by cbv

-- asrc_80_1_0_call_handler_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.skip,99,1,2)) (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 1) := by cbv

-- asrc_80_1_0_call_both_good=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.get 1 .currHeap,99,1,2)) (.inr 99) (some (.get 2 .currHeap,3,4))) : HolProg 1) := by cbv

-- asrc_80_1_0_inst_ignored=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.inst (.const 99 0)) : HolProg 1) := by cbv

-- asrc_80_1_0_skip=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 1) := by cbv

-- asrc_80_1_0_jump=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.jumpLower 900 901 902 : HolProg 1) := by cbv

-- asrc_80_1_0_alloc=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.alloc 900 : HolProg 1) := by cbv

-- asrc_80_1_0_raise=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.raise 900 : HolProg 1) := by cbv

-- asrc_80_1_0_ret=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.ret 900 : HolProg 1) := by cbv

-- asrc_80_1_0_break=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.break 900 : HolProg 1) := by cbv

-- asrc_80_1_0_continue=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.continue 900 : HolProg 1) := by cbv

-- asrc_80_1_0_ffi=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.ffi (Basis.Pure.MlString.ofString "abc") 900 901 902 903 904 : HolProg 1) := by cbv

-- asrc_80_1_0_tick=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.tick : HolProg 1) := by cbv

-- asrc_80_1_0_loc=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.locValue 900 901 902 : HolProg 1) := by cbv

-- asrc_80_1_0_install=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.install 900 901 902 903 904 : HolProg 1) := by cbv

-- asrc_80_1_0_share=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.shMemOp .load 900 (.addr 901 0) : HolProg 1) := by cbv

-- asrc_80_1_0_code=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.codeBufferWrite 900 901 : HolProg 1) := by cbv

-- asrc_80_1_0_data=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.dataBufferWrite 900 901 : HolProg 1) := by cbv

-- asrc_80_1_0_raw=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.rawCall 900 : HolProg 1) := by cbv

-- asrc_80_1_0_stackalloc=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.stackAlloc 900 : HolProg 1) := by cbv

-- asrc_80_1_0_stackfree=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.stackFree 900 : HolProg 1) := by cbv

-- asrc_80_1_0_halt=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.halt 900 : HolProg 1) := by cbv

-- asrc_80_1_1_get_last=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.get 5 .currHeap) : HolProg 1) := by cbv

-- asrc_80_1_1_get_bound=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.get 6 .currHeap) : HolProg 1) := by cbv

-- asrc_80_1_1_set=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.set .currHeap 1) : HolProg 1) := by cbv

-- asrc_80_1_1_store_ignored_second=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackStore 1 99) : HolProg 1) := by cbv

-- asrc_80_1_1_store_first_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackStore 6 1) : HolProg 1) := by cbv

-- asrc_80_1_1_load_ignored_second=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackLoad 1 99) : HolProg 1) := by cbv

-- asrc_80_1_1_load_first_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackLoad 6 1) : HolProg 1) := by cbv

-- asrc_80_1_1_get_size=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackGetSize 1) : HolProg 1) := by cbv

-- asrc_80_1_1_set_size_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackSetSize 6) : HolProg 1) := by cbv

-- asrc_80_1_1_heap=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.opCurrHeap .add 1 2) : HolProg 1) := by cbv

-- asrc_80_1_1_store_any_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackStoreAny 1 6) : HolProg 1) := by cbv

-- asrc_80_1_1_load_any=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackLoadAny 1 2) : HolProg 1) := by cbv

-- asrc_80_1_1_bitmap_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.bitmapLoad 6 1) : HolProg 1) := by cbv

-- asrc_80_1_1_consts=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.storeConsts 1 2 (some 99)) : HolProg 1) := by cbv

-- asrc_80_1_1_seq_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.seq (.get 1 .currHeap) (.get 6 .currHeap)) : HolProg 1) := by cbv

-- asrc_80_1_1_if_ignored_condition=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.ite .equal 99 (.reg 99) .skip .skip) : HolProg 1) := by cbv

-- asrc_80_1_1_loop_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.loop (.get 6 .currHeap)) : HolProg 1) := by cbv

-- asrc_80_1_1_call_none_ignored=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call none (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 1) := by cbv

-- asrc_80_1_1_call_body_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call (some (.get 6 .currHeap,99,1,2)) (.inr 99) none) : HolProg 1) := by cbv

-- asrc_80_1_1_call_handler_bad=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call (some (.skip,99,1,2)) (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 1) := by cbv

-- asrc_80_1_1_call_both_good=F
example (c : AsmConfigExact 80) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call (some (.get 1 .currHeap,99,1,2)) (.inr 99) (some (.get 2 .currHeap,3,4))) : HolProg 1) := by cbv

-- asrc_80_1_1_inst_ignored=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.inst (.const 99 0)) : HolProg 1) := by cbv

-- asrc_80_1_1_skip=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.skip : HolProg 1) := by cbv

-- asrc_80_1_1_jump=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.jumpLower 900 901 902 : HolProg 1) := by cbv

-- asrc_80_1_1_alloc=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.alloc 900 : HolProg 1) := by cbv

-- asrc_80_1_1_raise=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.raise 900 : HolProg 1) := by cbv

-- asrc_80_1_1_ret=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.ret 900 : HolProg 1) := by cbv

-- asrc_80_1_1_break=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.break 900 : HolProg 1) := by cbv

-- asrc_80_1_1_continue=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.continue 900 : HolProg 1) := by cbv

-- asrc_80_1_1_ffi=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.ffi (Basis.Pure.MlString.ofString "abc") 900 901 902 903 904 : HolProg 1) := by cbv

-- asrc_80_1_1_tick=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.tick : HolProg 1) := by cbv

-- asrc_80_1_1_loc=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.locValue 900 901 902 : HolProg 1) := by cbv

-- asrc_80_1_1_install=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.install 900 901 902 903 904 : HolProg 1) := by cbv

-- asrc_80_1_1_share=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.shMemOp .load 900 (.addr 901 0) : HolProg 1) := by cbv

-- asrc_80_1_1_code=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.codeBufferWrite 900 901 : HolProg 1) := by cbv

-- asrc_80_1_1_data=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.dataBufferWrite 900 901 : HolProg 1) := by cbv

-- asrc_80_1_1_raw=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.rawCall 900 : HolProg 1) := by cbv

-- asrc_80_1_1_stackalloc=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.stackAlloc 900 : HolProg 1) := by cbv

-- asrc_80_1_1_stackfree=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.stackFree 900 : HolProg 1) := by cbv

-- asrc_80_1_1_halt=T
example (c : AsmConfigExact 80) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.halt 900 : HolProg 1) := by cbv

-- asrc_2_64_0_get_last=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.get 5 .currHeap) : HolProg 64) := by cbv

-- asrc_2_64_0_get_bound=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.get 6 .currHeap) : HolProg 64) := by cbv

-- asrc_2_64_0_set=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.set .currHeap 1) : HolProg 64) := by cbv

-- asrc_2_64_0_store_ignored_second=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStore 1 99) : HolProg 64) := by cbv

-- asrc_2_64_0_store_first_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStore 6 1) : HolProg 64) := by cbv

-- asrc_2_64_0_load_ignored_second=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoad 1 99) : HolProg 64) := by cbv

-- asrc_2_64_0_load_first_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoad 6 1) : HolProg 64) := by cbv

-- asrc_2_64_0_get_size=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackGetSize 1) : HolProg 64) := by cbv

-- asrc_2_64_0_set_size_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackSetSize 6) : HolProg 64) := by cbv

-- asrc_2_64_0_heap=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.opCurrHeap .add 1 2) : HolProg 64) := by cbv

-- asrc_2_64_0_store_any_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStoreAny 1 6) : HolProg 64) := by cbv

-- asrc_2_64_0_load_any=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoadAny 1 2) : HolProg 64) := by cbv

-- asrc_2_64_0_bitmap_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.bitmapLoad 6 1) : HolProg 64) := by cbv

-- asrc_2_64_0_consts=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.storeConsts 1 2 (some 99)) : HolProg 64) := by cbv

-- asrc_2_64_0_seq_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.seq (.get 1 .currHeap) (.get 6 .currHeap)) : HolProg 64) := by cbv

-- asrc_2_64_0_if_ignored_condition=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.ite .equal 99 (.reg 99) .skip .skip) : HolProg 64) := by cbv

-- asrc_2_64_0_loop_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.loop (.get 6 .currHeap)) : HolProg 64) := by cbv

-- asrc_2_64_0_call_none_ignored=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call none (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 64) := by cbv

-- asrc_2_64_0_call_body_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.get 6 .currHeap,99,1,2)) (.inr 99) none) : HolProg 64) := by cbv

-- asrc_2_64_0_call_handler_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.skip,99,1,2)) (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 64) := by cbv

-- asrc_2_64_0_call_both_good=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.get 1 .currHeap,99,1,2)) (.inr 99) (some (.get 2 .currHeap,3,4))) : HolProg 64) := by cbv

-- asrc_2_64_0_inst_ignored=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.inst (.const 99 0)) : HolProg 64) := by cbv

-- asrc_2_64_0_skip=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 64) := by cbv

-- asrc_2_64_0_jump=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.jumpLower 900 901 902 : HolProg 64) := by cbv

-- asrc_2_64_0_alloc=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.alloc 900 : HolProg 64) := by cbv

-- asrc_2_64_0_raise=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.raise 900 : HolProg 64) := by cbv

-- asrc_2_64_0_ret=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.ret 900 : HolProg 64) := by cbv

-- asrc_2_64_0_break=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.break 900 : HolProg 64) := by cbv

-- asrc_2_64_0_continue=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.continue 900 : HolProg 64) := by cbv

-- asrc_2_64_0_ffi=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.ffi (Basis.Pure.MlString.ofString "abc") 900 901 902 903 904 : HolProg 64) := by cbv

-- asrc_2_64_0_tick=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.tick : HolProg 64) := by cbv

-- asrc_2_64_0_loc=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.locValue 900 901 902 : HolProg 64) := by cbv

-- asrc_2_64_0_install=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.install 900 901 902 903 904 : HolProg 64) := by cbv

-- asrc_2_64_0_share=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.shMemOp .load 900 (.addr 901 0) : HolProg 64) := by cbv

-- asrc_2_64_0_code=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.codeBufferWrite 900 901 : HolProg 64) := by cbv

-- asrc_2_64_0_data=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.dataBufferWrite 900 901 : HolProg 64) := by cbv

-- asrc_2_64_0_raw=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.rawCall 900 : HolProg 64) := by cbv

-- asrc_2_64_0_stackalloc=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.stackAlloc 900 : HolProg 64) := by cbv

-- asrc_2_64_0_stackfree=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.stackFree 900 : HolProg 64) := by cbv

-- asrc_2_64_0_halt=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.halt 900 : HolProg 64) := by cbv

-- asrc_2_64_1_get_last=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.get 5 .currHeap) : HolProg 64) := by cbv

-- asrc_2_64_1_get_bound=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.get 6 .currHeap) : HolProg 64) := by cbv

-- asrc_2_64_1_set=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.set .currHeap 1) : HolProg 64) := by cbv

-- asrc_2_64_1_store_ignored_second=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackStore 1 99) : HolProg 64) := by cbv

-- asrc_2_64_1_store_first_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackStore 6 1) : HolProg 64) := by cbv

-- asrc_2_64_1_load_ignored_second=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackLoad 1 99) : HolProg 64) := by cbv

-- asrc_2_64_1_load_first_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackLoad 6 1) : HolProg 64) := by cbv

-- asrc_2_64_1_get_size=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackGetSize 1) : HolProg 64) := by cbv

-- asrc_2_64_1_set_size_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackSetSize 6) : HolProg 64) := by cbv

-- asrc_2_64_1_heap=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.opCurrHeap .add 1 2) : HolProg 64) := by cbv

-- asrc_2_64_1_store_any_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackStoreAny 1 6) : HolProg 64) := by cbv

-- asrc_2_64_1_load_any=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackLoadAny 1 2) : HolProg 64) := by cbv

-- asrc_2_64_1_bitmap_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.bitmapLoad 6 1) : HolProg 64) := by cbv

-- asrc_2_64_1_consts=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.storeConsts 1 2 (some 99)) : HolProg 64) := by cbv

-- asrc_2_64_1_seq_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.seq (.get 1 .currHeap) (.get 6 .currHeap)) : HolProg 64) := by cbv

-- asrc_2_64_1_if_ignored_condition=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.ite .equal 99 (.reg 99) .skip .skip) : HolProg 64) := by cbv

-- asrc_2_64_1_loop_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.loop (.get 6 .currHeap)) : HolProg 64) := by cbv

-- asrc_2_64_1_call_none_ignored=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call none (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 64) := by cbv

-- asrc_2_64_1_call_body_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call (some (.get 6 .currHeap,99,1,2)) (.inr 99) none) : HolProg 64) := by cbv

-- asrc_2_64_1_call_handler_bad=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call (some (.skip,99,1,2)) (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 64) := by cbv

-- asrc_2_64_1_call_both_good=F
example (c : AsmConfigExact 2) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call (some (.get 1 .currHeap,99,1,2)) (.inr 99) (some (.get 2 .currHeap,3,4))) : HolProg 64) := by cbv

-- asrc_2_64_1_inst_ignored=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.inst (.const 99 0)) : HolProg 64) := by cbv

-- asrc_2_64_1_skip=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.skip : HolProg 64) := by cbv

-- asrc_2_64_1_jump=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.jumpLower 900 901 902 : HolProg 64) := by cbv

-- asrc_2_64_1_alloc=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.alloc 900 : HolProg 64) := by cbv

-- asrc_2_64_1_raise=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.raise 900 : HolProg 64) := by cbv

-- asrc_2_64_1_ret=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.ret 900 : HolProg 64) := by cbv

-- asrc_2_64_1_break=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.break 900 : HolProg 64) := by cbv

-- asrc_2_64_1_continue=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.continue 900 : HolProg 64) := by cbv

-- asrc_2_64_1_ffi=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.ffi (Basis.Pure.MlString.ofString "abc") 900 901 902 903 904 : HolProg 64) := by cbv

-- asrc_2_64_1_tick=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.tick : HolProg 64) := by cbv

-- asrc_2_64_1_loc=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.locValue 900 901 902 : HolProg 64) := by cbv

-- asrc_2_64_1_install=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.install 900 901 902 903 904 : HolProg 64) := by cbv

-- asrc_2_64_1_share=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.shMemOp .load 900 (.addr 901 0) : HolProg 64) := by cbv

-- asrc_2_64_1_code=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.codeBufferWrite 900 901 : HolProg 64) := by cbv

-- asrc_2_64_1_data=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.dataBufferWrite 900 901 : HolProg 64) := by cbv

-- asrc_2_64_1_raw=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.rawCall 900 : HolProg 64) := by cbv

-- asrc_2_64_1_stackalloc=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.stackAlloc 900 : HolProg 64) := by cbv

-- asrc_2_64_1_stackfree=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.stackFree 900 : HolProg 64) := by cbv

-- asrc_2_64_1_halt=T
example (c : AsmConfigExact 2) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.halt 900 : HolProg 64) := by cbv

-- asrc_64_2_0_get_last=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.get 5 .currHeap) : HolProg 2) := by cbv

-- asrc_64_2_0_get_bound=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.get 6 .currHeap) : HolProg 2) := by cbv

-- asrc_64_2_0_set=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.set .currHeap 1) : HolProg 2) := by cbv

-- asrc_64_2_0_store_ignored_second=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStore 1 99) : HolProg 2) := by cbv

-- asrc_64_2_0_store_first_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStore 6 1) : HolProg 2) := by cbv

-- asrc_64_2_0_load_ignored_second=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoad 1 99) : HolProg 2) := by cbv

-- asrc_64_2_0_load_first_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoad 6 1) : HolProg 2) := by cbv

-- asrc_64_2_0_get_size=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackGetSize 1) : HolProg 2) := by cbv

-- asrc_64_2_0_set_size_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackSetSize 6) : HolProg 2) := by cbv

-- asrc_64_2_0_heap=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.opCurrHeap .add 1 2) : HolProg 2) := by cbv

-- asrc_64_2_0_store_any_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStoreAny 1 6) : HolProg 2) := by cbv

-- asrc_64_2_0_load_any=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoadAny 1 2) : HolProg 2) := by cbv

-- asrc_64_2_0_bitmap_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.bitmapLoad 6 1) : HolProg 2) := by cbv

-- asrc_64_2_0_consts=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.storeConsts 1 2 (some 99)) : HolProg 2) := by cbv

-- asrc_64_2_0_seq_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.seq (.get 1 .currHeap) (.get 6 .currHeap)) : HolProg 2) := by cbv

-- asrc_64_2_0_if_ignored_condition=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.ite .equal 99 (.reg 99) .skip .skip) : HolProg 2) := by cbv

-- asrc_64_2_0_loop_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.loop (.get 6 .currHeap)) : HolProg 2) := by cbv

-- asrc_64_2_0_call_none_ignored=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call none (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 2) := by cbv

-- asrc_64_2_0_call_body_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.get 6 .currHeap,99,1,2)) (.inr 99) none) : HolProg 2) := by cbv

-- asrc_64_2_0_call_handler_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.skip,99,1,2)) (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 2) := by cbv

-- asrc_64_2_0_call_both_good=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.get 1 .currHeap,99,1,2)) (.inr 99) (some (.get 2 .currHeap,3,4))) : HolProg 2) := by cbv

-- asrc_64_2_0_inst_ignored=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.inst (.const 99 0)) : HolProg 2) := by cbv

-- asrc_64_2_0_skip=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 2) := by cbv

-- asrc_64_2_0_jump=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.jumpLower 900 901 902 : HolProg 2) := by cbv

-- asrc_64_2_0_alloc=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.alloc 900 : HolProg 2) := by cbv

-- asrc_64_2_0_raise=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.raise 900 : HolProg 2) := by cbv

-- asrc_64_2_0_ret=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.ret 900 : HolProg 2) := by cbv

-- asrc_64_2_0_break=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.break 900 : HolProg 2) := by cbv

-- asrc_64_2_0_continue=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.continue 900 : HolProg 2) := by cbv

-- asrc_64_2_0_ffi=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.ffi (Basis.Pure.MlString.ofString "abc") 900 901 902 903 904 : HolProg 2) := by cbv

-- asrc_64_2_0_tick=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.tick : HolProg 2) := by cbv

-- asrc_64_2_0_loc=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.locValue 900 901 902 : HolProg 2) := by cbv

-- asrc_64_2_0_install=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.install 900 901 902 903 904 : HolProg 2) := by cbv

-- asrc_64_2_0_share=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.shMemOp .load 900 (.addr 901 0) : HolProg 2) := by cbv

-- asrc_64_2_0_code=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.codeBufferWrite 900 901 : HolProg 2) := by cbv

-- asrc_64_2_0_data=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.dataBufferWrite 900 901 : HolProg 2) := by cbv

-- asrc_64_2_0_raw=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.rawCall 900 : HolProg 2) := by cbv

-- asrc_64_2_0_stackalloc=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.stackAlloc 900 : HolProg 2) := by cbv

-- asrc_64_2_0_stackfree=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.stackFree 900 : HolProg 2) := by cbv

-- asrc_64_2_0_halt=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.halt 900 : HolProg 2) := by cbv

-- asrc_64_2_1_get_last=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.get 5 .currHeap) : HolProg 2) := by cbv

-- asrc_64_2_1_get_bound=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.get 6 .currHeap) : HolProg 2) := by cbv

-- asrc_64_2_1_set=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.set .currHeap 1) : HolProg 2) := by cbv

-- asrc_64_2_1_store_ignored_second=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackStore 1 99) : HolProg 2) := by cbv

-- asrc_64_2_1_store_first_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackStore 6 1) : HolProg 2) := by cbv

-- asrc_64_2_1_load_ignored_second=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackLoad 1 99) : HolProg 2) := by cbv

-- asrc_64_2_1_load_first_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackLoad 6 1) : HolProg 2) := by cbv

-- asrc_64_2_1_get_size=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackGetSize 1) : HolProg 2) := by cbv

-- asrc_64_2_1_set_size_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackSetSize 6) : HolProg 2) := by cbv

-- asrc_64_2_1_heap=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.opCurrHeap .add 1 2) : HolProg 2) := by cbv

-- asrc_64_2_1_store_any_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackStoreAny 1 6) : HolProg 2) := by cbv

-- asrc_64_2_1_load_any=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackLoadAny 1 2) : HolProg 2) := by cbv

-- asrc_64_2_1_bitmap_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.bitmapLoad 6 1) : HolProg 2) := by cbv

-- asrc_64_2_1_consts=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.storeConsts 1 2 (some 99)) : HolProg 2) := by cbv

-- asrc_64_2_1_seq_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.seq (.get 1 .currHeap) (.get 6 .currHeap)) : HolProg 2) := by cbv

-- asrc_64_2_1_if_ignored_condition=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.ite .equal 99 (.reg 99) .skip .skip) : HolProg 2) := by cbv

-- asrc_64_2_1_loop_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.loop (.get 6 .currHeap)) : HolProg 2) := by cbv

-- asrc_64_2_1_call_none_ignored=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call none (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 2) := by cbv

-- asrc_64_2_1_call_body_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call (some (.get 6 .currHeap,99,1,2)) (.inr 99) none) : HolProg 2) := by cbv

-- asrc_64_2_1_call_handler_bad=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call (some (.skip,99,1,2)) (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 2) := by cbv

-- asrc_64_2_1_call_both_good=F
example (c : AsmConfigExact 64) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call (some (.get 1 .currHeap,99,1,2)) (.inr 99) (some (.get 2 .currHeap,3,4))) : HolProg 2) := by cbv

-- asrc_64_2_1_inst_ignored=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.inst (.const 99 0)) : HolProg 2) := by cbv

-- asrc_64_2_1_skip=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.skip : HolProg 2) := by cbv

-- asrc_64_2_1_jump=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.jumpLower 900 901 902 : HolProg 2) := by cbv

-- asrc_64_2_1_alloc=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.alloc 900 : HolProg 2) := by cbv

-- asrc_64_2_1_raise=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.raise 900 : HolProg 2) := by cbv

-- asrc_64_2_1_ret=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.ret 900 : HolProg 2) := by cbv

-- asrc_64_2_1_break=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.break 900 : HolProg 2) := by cbv

-- asrc_64_2_1_continue=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.continue 900 : HolProg 2) := by cbv

-- asrc_64_2_1_ffi=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.ffi (Basis.Pure.MlString.ofString "abc") 900 901 902 903 904 : HolProg 2) := by cbv

-- asrc_64_2_1_tick=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.tick : HolProg 2) := by cbv

-- asrc_64_2_1_loc=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.locValue 900 901 902 : HolProg 2) := by cbv

-- asrc_64_2_1_install=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.install 900 901 902 903 904 : HolProg 2) := by cbv

-- asrc_64_2_1_share=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.shMemOp .load 900 (.addr 901 0) : HolProg 2) := by cbv

-- asrc_64_2_1_code=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.codeBufferWrite 900 901 : HolProg 2) := by cbv

-- asrc_64_2_1_data=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.dataBufferWrite 900 901 : HolProg 2) := by cbv

-- asrc_64_2_1_raw=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.rawCall 900 : HolProg 2) := by cbv

-- asrc_64_2_1_stackalloc=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.stackAlloc 900 : HolProg 2) := by cbv

-- asrc_64_2_1_stackfree=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.stackFree 900 : HolProg 2) := by cbv

-- asrc_64_2_1_halt=T
example (c : AsmConfigExact 64) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.halt 900 : HolProg 2) := by cbv

-- asrc_8_8_0_get_last=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.get 5 .currHeap) : HolProg 8) := by cbv

-- asrc_8_8_0_get_bound=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.get 6 .currHeap) : HolProg 8) := by cbv

-- asrc_8_8_0_set=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.set .currHeap 1) : HolProg 8) := by cbv

-- asrc_8_8_0_store_ignored_second=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStore 1 99) : HolProg 8) := by cbv

-- asrc_8_8_0_store_first_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStore 6 1) : HolProg 8) := by cbv

-- asrc_8_8_0_load_ignored_second=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoad 1 99) : HolProg 8) := by cbv

-- asrc_8_8_0_load_first_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoad 6 1) : HolProg 8) := by cbv

-- asrc_8_8_0_get_size=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackGetSize 1) : HolProg 8) := by cbv

-- asrc_8_8_0_set_size_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackSetSize 6) : HolProg 8) := by cbv

-- asrc_8_8_0_heap=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.opCurrHeap .add 1 2) : HolProg 8) := by cbv

-- asrc_8_8_0_store_any_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStoreAny 1 6) : HolProg 8) := by cbv

-- asrc_8_8_0_load_any=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoadAny 1 2) : HolProg 8) := by cbv

-- asrc_8_8_0_bitmap_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.bitmapLoad 6 1) : HolProg 8) := by cbv

-- asrc_8_8_0_consts=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.storeConsts 1 2 (some 99)) : HolProg 8) := by cbv

-- asrc_8_8_0_seq_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.seq (.get 1 .currHeap) (.get 6 .currHeap)) : HolProg 8) := by cbv

-- asrc_8_8_0_if_ignored_condition=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.ite .equal 99 (.reg 99) .skip .skip) : HolProg 8) := by cbv

-- asrc_8_8_0_loop_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.loop (.get 6 .currHeap)) : HolProg 8) := by cbv

-- asrc_8_8_0_call_none_ignored=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call none (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 8) := by cbv

-- asrc_8_8_0_call_body_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.get 6 .currHeap,99,1,2)) (.inr 99) none) : HolProg 8) := by cbv

-- asrc_8_8_0_call_handler_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.skip,99,1,2)) (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 8) := by cbv

-- asrc_8_8_0_call_both_good=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.get 1 .currHeap,99,1,2)) (.inr 99) (some (.get 2 .currHeap,3,4))) : HolProg 8) := by cbv

-- asrc_8_8_0_inst_ignored=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.inst (.const 99 0)) : HolProg 8) := by cbv

-- asrc_8_8_0_skip=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 8) := by cbv

-- asrc_8_8_0_jump=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.jumpLower 900 901 902 : HolProg 8) := by cbv

-- asrc_8_8_0_alloc=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.alloc 900 : HolProg 8) := by cbv

-- asrc_8_8_0_raise=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.raise 900 : HolProg 8) := by cbv

-- asrc_8_8_0_ret=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.ret 900 : HolProg 8) := by cbv

-- asrc_8_8_0_break=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.break 900 : HolProg 8) := by cbv

-- asrc_8_8_0_continue=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.continue 900 : HolProg 8) := by cbv

-- asrc_8_8_0_ffi=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.ffi (Basis.Pure.MlString.ofString "abc") 900 901 902 903 904 : HolProg 8) := by cbv

-- asrc_8_8_0_tick=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.tick : HolProg 8) := by cbv

-- asrc_8_8_0_loc=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.locValue 900 901 902 : HolProg 8) := by cbv

-- asrc_8_8_0_install=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.install 900 901 902 903 904 : HolProg 8) := by cbv

-- asrc_8_8_0_share=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.shMemOp .load 900 (.addr 901 0) : HolProg 8) := by cbv

-- asrc_8_8_0_code=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.codeBufferWrite 900 901 : HolProg 8) := by cbv

-- asrc_8_8_0_data=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.dataBufferWrite 900 901 : HolProg 8) := by cbv

-- asrc_8_8_0_raw=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.rawCall 900 : HolProg 8) := by cbv

-- asrc_8_8_0_stackalloc=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.stackAlloc 900 : HolProg 8) := by cbv

-- asrc_8_8_0_stackfree=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.stackFree 900 : HolProg 8) := by cbv

-- asrc_8_8_0_halt=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} (.halt 900 : HolProg 8) := by cbv

-- asrc_8_8_1_get_last=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.get 5 .currHeap) : HolProg 8) := by cbv

-- asrc_8_8_1_get_bound=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.get 6 .currHeap) : HolProg 8) := by cbv

-- asrc_8_8_1_set=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.set .currHeap 1) : HolProg 8) := by cbv

-- asrc_8_8_1_store_ignored_second=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackStore 1 99) : HolProg 8) := by cbv

-- asrc_8_8_1_store_first_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackStore 6 1) : HolProg 8) := by cbv

-- asrc_8_8_1_load_ignored_second=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackLoad 1 99) : HolProg 8) := by cbv

-- asrc_8_8_1_load_first_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackLoad 6 1) : HolProg 8) := by cbv

-- asrc_8_8_1_get_size=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackGetSize 1) : HolProg 8) := by cbv

-- asrc_8_8_1_set_size_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackSetSize 6) : HolProg 8) := by cbv

-- asrc_8_8_1_heap=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.opCurrHeap .add 1 2) : HolProg 8) := by cbv

-- asrc_8_8_1_store_any_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackStoreAny 1 6) : HolProg 8) := by cbv

-- asrc_8_8_1_load_any=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.stackLoadAny 1 2) : HolProg 8) := by cbv

-- asrc_8_8_1_bitmap_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.bitmapLoad 6 1) : HolProg 8) := by cbv

-- asrc_8_8_1_consts=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.storeConsts 1 2 (some 99)) : HolProg 8) := by cbv

-- asrc_8_8_1_seq_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.seq (.get 1 .currHeap) (.get 6 .currHeap)) : HolProg 8) := by cbv

-- asrc_8_8_1_if_ignored_condition=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.ite .equal 99 (.reg 99) .skip .skip) : HolProg 8) := by cbv

-- asrc_8_8_1_loop_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.loop (.get 6 .currHeap)) : HolProg 8) := by cbv

-- asrc_8_8_1_call_none_ignored=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call none (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 8) := by cbv

-- asrc_8_8_1_call_body_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call (some (.get 6 .currHeap,99,1,2)) (.inr 99) none) : HolProg 8) := by cbv

-- asrc_8_8_1_call_handler_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call (some (.skip,99,1,2)) (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 8) := by cbv

-- asrc_8_8_1_call_both_good=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.call (some (.get 1 .currHeap,99,1,2)) (.inr 99) (some (.get 2 .currHeap,3,4))) : HolProg 8) := by cbv

-- asrc_8_8_1_inst_ignored=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} ((.inst (.const 99 0)) : HolProg 8) := by cbv

-- asrc_8_8_1_skip=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.skip : HolProg 8) := by cbv

-- asrc_8_8_1_jump=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.jumpLower 900 901 902 : HolProg 8) := by cbv

-- asrc_8_8_1_alloc=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.alloc 900 : HolProg 8) := by cbv

-- asrc_8_8_1_raise=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.raise 900 : HolProg 8) := by cbv

-- asrc_8_8_1_ret=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.ret 900 : HolProg 8) := by cbv

-- asrc_8_8_1_break=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.break 900 : HolProg 8) := by cbv

-- asrc_8_8_1_continue=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.continue 900 : HolProg 8) := by cbv

-- asrc_8_8_1_ffi=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.ffi (Basis.Pure.MlString.ofString "abc") 900 901 902 903 904 : HolProg 8) := by cbv

-- asrc_8_8_1_tick=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.tick : HolProg 8) := by cbv

-- asrc_8_8_1_loc=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.locValue 900 901 902 : HolProg 8) := by cbv

-- asrc_8_8_1_install=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.install 900 901 902 903 904 : HolProg 8) := by cbv

-- asrc_8_8_1_share=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.shMemOp .load 900 (.addr 901 0) : HolProg 8) := by cbv

-- asrc_8_8_1_code=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.codeBufferWrite 900 901 : HolProg 8) := by cbv

-- asrc_8_8_1_data=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.dataBufferWrite 900 901 : HolProg 8) := by cbv

-- asrc_8_8_1_raw=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.rawCall 900 : HolProg 8) := by cbv

-- asrc_8_8_1_stackalloc=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.stackAlloc 900 : HolProg 8) := by cbv

-- asrc_8_8_1_stackfree=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.stackFree 900 : HolProg 8) := by cbv

-- asrc_8_8_1_halt=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424]} (.halt 900 : HolProg 8) := by cbv

end Flapjack.Test.StackPropsRemoveIndependentParity
