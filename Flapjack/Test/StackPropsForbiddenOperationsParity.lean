import Flapjack.Compiler.Backend.StackProps.ForbiddenOperations

/-! Same-input original StackProps predicate regressions. All constructor
families and both independent optional Call bodies are covered. These kernel
checks are regression evidence, not HOL-to-Lean equivalence. -/
namespace Flapjack.Test.StackPropsForbiddenOperationsParity
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps

-- forbid_skip
example : (noInstall (.skip : HolProg 64), noShmemop (.skip : HolProg 64)) = (true,true) := by rfl

-- forbid_inst
example : (noInstall (.inst (.const 0 1) : HolProg 64), noShmemop (.inst (.const 0 1) : HolProg 64)) = (true,true) := by rfl

-- forbid_get
example : (noInstall (.get 0 .handler : HolProg 64), noShmemop (.get 0 .handler : HolProg 64)) = (true,true) := by rfl

-- forbid_set
example : (noInstall (.set .handler 0 : HolProg 64), noShmemop (.set .handler 0 : HolProg 64)) = (true,true) := by rfl

-- forbid_heap
example : (noInstall (.opCurrHeap .add 0 1 : HolProg 64), noShmemop (.opCurrHeap .add 0 1 : HolProg 64)) = (true,true) := by rfl

-- forbid_call_empty
example : (noInstall (.call none (.inl 7) none : HolProg 64), noShmemop (.call none (.inl 7) none : HolProg 64)) = (true,true) := by rfl

-- forbid_seq
example : (noInstall (.seq .skip .tick : HolProg 64), noShmemop (.seq .skip .tick : HolProg 64)) = (true,true) := by rfl

-- forbid_if
example : (noInstall (.ite .equal 0 (.reg 1) .skip .tick : HolProg 64), noShmemop (.ite .equal 0 (.reg 1) .skip .tick : HolProg 64)) = (true,true) := by rfl

-- forbid_loop
example : (noInstall (.loop .skip : HolProg 64), noShmemop (.loop .skip : HolProg 64)) = (true,true) := by rfl

-- forbid_jump
example : (noInstall (.jumpLower 0 1 7 : HolProg 64), noShmemop (.jumpLower 0 1 7 : HolProg 64)) = (true,true) := by rfl

-- forbid_alloc
example : (noInstall (.alloc 3 : HolProg 64), noShmemop (.alloc 3 : HolProg 64)) = (true,true) := by rfl

-- forbid_store_consts
example : (noInstall (.storeConsts 0 1 (some 7) : HolProg 64), noShmemop (.storeConsts 0 1 (some 7) : HolProg 64)) = (true,true) := by rfl

-- forbid_raise
example : (noInstall (.raise 0 : HolProg 64), noShmemop (.raise 0 : HolProg 64)) = (true,true) := by rfl

-- forbid_return
example : (noInstall (.ret 0 : HolProg 64), noShmemop (.ret 0 : HolProg 64)) = (true,true) := by rfl

-- forbid_break
example : (noInstall (.break 7 : HolProg 64), noShmemop (.break 7 : HolProg 64)) = (true,true) := by rfl

-- forbid_continue
example : (noInstall (.continue 7 : HolProg 64), noShmemop (.continue 7 : HolProg 64)) = (true,true) := by rfl

-- forbid_ffi
example : (noInstall (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 0 1 2 3 4 : HolProg 64), noShmemop (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 0 1 2 3 4 : HolProg 64)) = (true,true) := by rfl

-- forbid_tick
example : (noInstall (.tick : HolProg 64), noShmemop (.tick : HolProg 64)) = (true,true) := by rfl

-- forbid_loc
example : (noInstall (.locValue 0 7 1 : HolProg 64), noShmemop (.locValue 0 7 1 : HolProg 64)) = (true,true) := by rfl

-- forbid_install
example : (noInstall (.install 0 1 2 3 4 : HolProg 64), noShmemop (.install 0 1 2 3 4 : HolProg 64)) = (false,true) := by rfl

-- forbid_shmem
example : (noInstall (.shMemOp .load 0 (.addr 1 0) : HolProg 64), noShmemop (.shMemOp .load 0 (.addr 1 0) : HolProg 64)) = (true,false) := by rfl

-- forbid_code_write
example : (noInstall (.codeBufferWrite 0 1 : HolProg 64), noShmemop (.codeBufferWrite 0 1 : HolProg 64)) = (true,true) := by rfl

-- forbid_data_write
example : (noInstall (.dataBufferWrite 0 1 : HolProg 64), noShmemop (.dataBufferWrite 0 1 : HolProg 64)) = (true,true) := by rfl

-- forbid_raw_call
example : (noInstall (.rawCall 7 : HolProg 64), noShmemop (.rawCall 7 : HolProg 64)) = (true,true) := by rfl

-- forbid_stack_alloc
example : (noInstall (.stackAlloc 2 : HolProg 64), noShmemop (.stackAlloc 2 : HolProg 64)) = (true,true) := by rfl

-- forbid_stack_free
example : (noInstall (.stackFree 2 : HolProg 64), noShmemop (.stackFree 2 : HolProg 64)) = (true,true) := by rfl

-- forbid_stack_store
example : (noInstall (.stackStore 0 1 : HolProg 64), noShmemop (.stackStore 0 1 : HolProg 64)) = (true,true) := by rfl

-- forbid_stack_store_any
example : (noInstall (.stackStoreAny 0 1 : HolProg 64), noShmemop (.stackStoreAny 0 1 : HolProg 64)) = (true,true) := by rfl

-- forbid_stack_load
example : (noInstall (.stackLoad 0 1 : HolProg 64), noShmemop (.stackLoad 0 1 : HolProg 64)) = (true,true) := by rfl

-- forbid_stack_load_any
example : (noInstall (.stackLoadAny 0 1 : HolProg 64), noShmemop (.stackLoadAny 0 1 : HolProg 64)) = (true,true) := by rfl

-- forbid_stack_get_size
example : (noInstall (.stackGetSize 0 : HolProg 64), noShmemop (.stackGetSize 0 : HolProg 64)) = (true,true) := by rfl

-- forbid_stack_set_size
example : (noInstall (.stackSetSize 0 : HolProg 64), noShmemop (.stackSetSize 0 : HolProg 64)) = (true,true) := by rfl

-- forbid_bitmap_load
example : (noInstall (.bitmapLoad 0 1 : HolProg 64), noShmemop (.bitmapLoad 0 1 : HolProg 64)) = (true,true) := by rfl

-- forbid_halt
example : (noInstall (.halt 0 : HolProg 64), noShmemop (.halt 0 : HolProg 64)) = (true,true) := by rfl

-- forbid_call_handler_install
example : (noInstall (.call none (.inr 0) (some (.install 0 1 2 3 4,7,5)) : HolProg 64), noShmemop (.call none (.inr 0) (some (.install 0 1 2 3 4,7,5)) : HolProg 64)) = (false,true) := by rfl

-- forbid_call_handler_shmem
example : (noInstall (.call none (.inl 7) (some (.shMemOp .store16 0 (.addr 1 0),7,5)) : HolProg 64), noShmemop (.call none (.inl 7) (some (.shMemOp .store16 0 (.addr 1 0),7,5)) : HolProg 64)) = (true,false) := by rfl

-- forbid_call_return_install
example : (noInstall (.call (some (.install 0 1 2 3 4,0,7,1)) (.inr 0) none : HolProg 64), noShmemop (.call (some (.install 0 1 2 3 4,0,7,1)) (.inr 0) none : HolProg 64)) = (false,true) := by rfl

-- forbid_call_return_shmem
example : (noInstall (.call (some (.shMemOp .store16 0 (.addr 1 0),0,7,1)) (.inl 7) none : HolProg 64), noShmemop (.call (some (.shMemOp .store16 0 (.addr 1 0),0,7,1)) (.inl 7) none : HolProg 64)) = (true,false) := by rfl

-- forbid_call_both
example : (noInstall (.call (some (.install 0 1 2 3 4,0,7,1)) (.inl 7) (some (.shMemOp .store16 0 (.addr 1 0),7,5)) : HolProg 64), noShmemop (.call (some (.install 0 1 2 3 4,0,7,1)) (.inl 7) (some (.shMemOp .store16 0 (.addr 1 0),7,5)) : HolProg 64)) = (false,false) := by rfl

-- forbid_call_safe
example : (noInstall (.call (some (.skip,0,7,1)) (.inl 7) (some (.tick,9,5)) : HolProg 64), noShmemop (.call (some (.skip,0,7,1)) (.inl 7) (some (.tick,9,5)) : HolProg 64)) = (true,true) := by rfl

-- forbid_seq_left
example : (noInstall (.seq (.install 0 1 2 3 4) .skip : HolProg 64), noShmemop (.seq (.install 0 1 2 3 4) .skip : HolProg 64)) = (false,true) := by rfl

-- forbid_seq_right
example : (noInstall (.seq .skip (.shMemOp .store16 0 (.addr 1 0)) : HolProg 64), noShmemop (.seq .skip (.shMemOp .store16 0 (.addr 1 0)) : HolProg 64)) = (true,false) := by rfl

-- forbid_if_left
example : (noInstall (.ite .equal 0 (.imm 0) (.install 0 1 2 3 4) .skip : HolProg 64), noShmemop (.ite .equal 0 (.imm 0) (.install 0 1 2 3 4) .skip : HolProg 64)) = (false,true) := by rfl

-- forbid_if_right
example : (noInstall (.ite .equal 0 (.imm 0) .skip (.shMemOp .store16 0 (.addr 1 0)) : HolProg 64), noShmemop (.ite .equal 0 (.imm 0) .skip (.shMemOp .store16 0 (.addr 1 0)) : HolProg 64)) = (true,false) := by rfl

-- forbid_loop_install
example : (noInstall (.loop (.install 0 1 2 3 4) : HolProg 64), noShmemop (.loop (.install 0 1 2 3 4) : HolProg 64)) = (false,true) := by rfl

-- forbid_loop_shmem
example : (noInstall (.loop (.shMemOp .store16 0 (.addr 1 0)) : HolProg 64), noShmemop (.loop (.shMemOp .store16 0 (.addr 1 0)) : HolProg 64)) = (true,false) := by rfl

-- Constructor payloads, target and labels do not impose bounds or ownership guards.
example {width : Nat} [NeZero width] (target : Sum Nat Nat) (a b c d e owner entry : Nat) :
    noInstall (.call none target (some (.install a b c d e,owner,entry)) : HolProg width) = false := by rfl

-- Arbitrary positive widths include the one-bit carrier.
example : noShmemop (.loop (.shMemOp .load32 0 (.addr 1 0)) : HolProg 1) = false := by rfl

end Flapjack.Test.StackPropsForbiddenOperationsParity
