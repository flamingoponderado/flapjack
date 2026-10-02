import Flapjack.Compiler.Backend.StackRemove.Comp

/-! All-constructor original comp regression fixtures. Expected clause trees are independent literals; previously checked native builders retain their original trees. -/

namespace Flapjack.Test.StackRemoveComp

open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

-- comp_get_heap
example : comp (width := 64) true (0, 0) 24 (.get 5 .currHeap) =
    (moveInst 5 26 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_get_store
example : comp (width := 64) true (0, 0) 24 (.get 5 .bitmapBase) =
    (.inst (.mem .load 5 (.addr 25 (BitVec.ofNat 64 18446744073709551528))) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_set_heap
example : comp (width := 64) true (0, 0) 24 (.set .currHeap 5) =
    (moveInst 26 5 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_set_temp
example : comp (width := 64) true (0, 0) 24 (.set (.temp 31) 5) =
    (.inst (.mem .store 5 (.addr 25 (BitVec.ofNat 64 18446744073709551232))) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_op_heap
example : comp (width := 64) true (0, 0) 24 (.opCurrHeap .xor 5 6) =
    (.inst (.arith (.binop .xor 5 6 (.reg 26))) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_free
example : comp (width := 64) true (0, 0) 24 (.stackFree 511) =
    (stackFree 24 511 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_alloc_false
example : comp (width := 64) false (0, 0) 24 (.stackAlloc 511) =
    (stackAlloc false 24 511 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_alloc_true
example : comp (width := 64) true (0, 0) 24 (.stackAlloc 511) =
    (stackAlloc true 24 511 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_store_direct
example : comp (width := 64) true (0, 4095) 24 (.stackStore 5 256) =
    (.inst (.mem .store 5 (.addr 24 2048)) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_load_direct
example : comp (width := 64) true (0, 4095) 24 (.stackLoad 5 256) =
    (.inst (.mem .load 5 (.addr 24 2048)) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_store_fallback
example : comp (width := 64) true (0, 0) 24 (.stackStore 5 256) =
    (stackStore 24 5 256 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_load_fallback
example : comp (width := 64) true (0, 0) 24 (.stackLoad 5 256) =
    (.seq (moveInst 5 24) (stackLoad 5 256) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_data_write
example : comp (width := 64) true (0, 0) 24 (.dataBufferWrite 5 6) =
    (.inst (.mem .store 6 (.addr 5 0)) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_load_any
example : comp (width := 64) true (0, 0) 24 (.stackLoadAny 5 6) =
    (.seq (.seq (moveInst 5 6) (addInst 5 24)) (.inst (.mem .load 5 (.addr 5 0))) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_store_any
example : comp (width := 64) true (0, 0) 24 (.stackStoreAny 5 6) =
    (.seq (.inst (.arith (.binop .add 24 24 (.reg 6)))) (.seq (.inst (.mem .store 5 (.addr 24 0))) (.inst (.arith (.binop .sub 24 24 (.reg 6))))) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_get_size_1
example : comp (width := 1) true (0, 0) 24 (.stackGetSize 5) =
    (.seq (.seq (moveInst 5 24) (subInst 5 25)) (rightShiftInst 5 3) : HolProg 1) := by
  simp only [comp]
  all_goals rfl

-- comp_set_size_1
example : comp (width := 1) true (0, 0) 24 (.stackSetSize 5) =
    (.seq (leftShiftInst 5 3) (.seq (moveInst 24 25) (addInst 24 5)) : HolProg 1) := by
  simp only [comp]
  all_goals rfl

-- comp_get_size_32
example : comp (width := 32) true (0, 0) 24 (.stackGetSize 5) =
    (.seq (.seq (moveInst 5 24) (subInst 5 25)) (rightShiftInst 5 2) : HolProg 32) := by
  simp only [comp]
  all_goals rfl

-- comp_set_size_32
example : comp (width := 32) true (0, 0) 24 (.stackSetSize 5) =
    (.seq (leftShiftInst 5 2) (.seq (moveInst 24 25) (addInst 24 5)) : HolProg 32) := by
  simp only [comp]
  all_goals rfl

-- comp_get_size_64
example : comp (width := 64) true (0, 0) 24 (.stackGetSize 5) =
    (.seq (.seq (moveInst 5 24) (subInst 5 25)) (rightShiftInst 5 3) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_set_size_64
example : comp (width := 64) true (0, 0) 24 (.stackSetSize 5) =
    (.seq (leftShiftInst 5 3) (.seq (moveInst 24 25) (addInst 24 5)) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_get_size_80
example : comp (width := 80) true (0, 0) 24 (.stackGetSize 5) =
    (.seq (.seq (moveInst 5 24) (subInst 5 25)) (rightShiftInst 5 3) : HolProg 80) := by
  simp only [comp]
  all_goals rfl

-- comp_set_size_80
example : comp (width := 80) true (0, 0) 24 (.stackSetSize 5) =
    (.seq (leftShiftInst 5 3) (.seq (moveInst 24 25) (addInst 24 5)) : HolProg 80) := by
  simp only [comp]
  all_goals rfl

-- comp_bitmap
example : comp (width := 64) true (0, 0) 24 (.bitmapLoad 5 6) =
    (listSeqHOL [.inst (.mem .load 5 (.addr 25 (storeOffset .bitmapBase))), addInst 5 6, leftShiftInst 5 3, .inst (.mem .load 5 (.addr 5 0))] : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_consts_none
example : comp (width := 64) true (0, 0) 24 (.storeConsts 5 6 none) =
    (listSeqHOL [.inst (.mem .load 6 (.addr 25 (storeOffset .bitmapBase))), addInst 6 1, leftShiftInst 6 3, copyLoop 5 6, moveInst 5 1, moveInst 6 1] : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_consts_some
example : comp (width := 64) true (0, 0) 24 (.storeConsts 5 6 (some 1234)) =
    (listSeqHOL [.inst (.mem .load 6 (.addr 25 (storeOffset .bitmapBase))), addInst 6 1, leftShiftInst 6 3, copyLoop 5 6, moveInst 5 1, moveInst 6 1] : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_seq
example : comp (width := 64) true (0, 0) 24 (.seq (.get 5 .currHeap) (.stackFree 1)) =
    (.seq (moveInst 5 26) (stackFree 24 1) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_if
example : comp (width := 64) true (0, 0) 24 (.ite .notLower 5 (.imm 7) (.stackFree 1) (.stackAlloc 1)) =
    (.ite .notLower 5 (.imm 7) (stackFree 24 1) (stackAlloc true 24 1) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_loop
example : comp (width := 64) true (0, 0) 24 (.loop (.stackLoad 5 256)) =
    (.loop (.seq (moveInst 5 24) (stackLoad 5 256)) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_call_0_0
example : comp (width := 64) true (0, 0) 24 (.call none (.inr 1234) none) =
    (.call none (.inr 1234) none : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_call_0_1
example : comp (width := 64) true (0, 0) 24 (.call none (.inr 1234) (some (.stackLoad 5 256, 11, 13))) =
    (.call none (.inr 1234) (some (.seq (moveInst 5 24) (stackLoad 5 256), 11, 13)) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_call_1_0
example : comp (width := 64) true (0, 0) 24 (.call (some (.stackFree 1, 42, 7, 9)) (.inr 1234) none) =
    (.call (some (stackFree 24 1, 42, 7, 9)) (.inr 1234) none : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_call_1_1
example : comp (width := 64) true (0, 0) 24 (.call (some (.stackFree 1, 42, 7, 9)) (.inr 1234) (some (.stackLoad 5 256, 11, 13))) =
    (.call (some (stackFree 24 1, 42, 7, 9)) (.inr 1234) (some (.seq (moveInst 5 24) (stackLoad 5 256), 11, 13)) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_signed_negative
example : comp (width := 8) true (128, 255) 24 (.stackLoad 1234 200) =
    (.inst (.mem .load 1234 (.addr 24 200)) : HolProg 8) := by
  simp only [comp]
  all_goals rfl

-- comp_signed_reversed
example : comp (width := 8) true (0, 255) 24 (.stackStore 1234 200) =
    (stackStore 24 1234 200 : HolProg 8) := by
  simp only [comp]
  all_goals rfl

-- comp_wrapped_zero
example : comp (width := 1) true (0, 0) 24 (.stackLoad 1234 511) =
    (.inst (.mem .load 1234 (.addr 24 0)) : HolProg 1) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_skip
example : comp (width := 64) true (0, 0) 24 (.skip) =
    (.skip : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_inst
example : comp (width := 64) true (0, 0) 24 (.inst (.const 1234 255)) =
    (.inst (.const 1234 255) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_jump
example : comp (width := 64) true (0, 0) 24 (.jumpLower 5 6 7) =
    (.jumpLower 5 6 7 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_alloc_runtime
example : comp (width := 64) true (0, 0) 24 (.alloc 1234) =
    (.alloc 1234 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_raise
example : comp (width := 64) true (0, 0) 24 (.raise 5) =
    (.raise 5 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_return
example : comp (width := 64) true (0, 0) 24 (.ret 5) =
    (.ret 5 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_break
example : comp (width := 64) true (0, 0) 24 (.break 7) =
    (.break 7 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_continue
example : comp (width := 64) true (0, 0) 24 (.continue 7) =
    (.continue 7 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_ffi
example : comp (width := 64) true (0, 0) 24 (.ffi (.implode [255, 0, 65]) 1 2 3 4 5) =
    (.ffi (.implode [255, 0, 65]) 1 2 3 4 5 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_tick
example : comp (width := 64) true (0, 0) 24 (.tick) =
    (.tick : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_loc
example : comp (width := 64) true (0, 0) 24 (.locValue 5 7 9) =
    (.locValue 5 7 9 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_install
example : comp (width := 64) true (0, 0) 24 (.install 1 2 3 4 5) =
    (.install 1 2 3 4 5 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_shared
example : comp (width := 64) true (0, 0) 24 (.shMemOp .store 5 (.addr 6 255)) =
    (.shMemOp .store 5 (.addr 6 255) : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_code_write
example : comp (width := 64) true (0, 0) 24 (.codeBufferWrite 5 6) =
    (.codeBufferWrite 5 6 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_raw
example : comp (width := 64) true (0, 0) 24 (.rawCall 1234) =
    (.rawCall 1234 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

-- comp_unchanged_halt
example : comp (width := 64) true (0, 0) 24 (.halt 5) =
    (.halt 5 : HolProg 64) := by
  simp only [comp]
  all_goals rfl

#print axioms comp

end Flapjack.Test.StackRemoveComp
