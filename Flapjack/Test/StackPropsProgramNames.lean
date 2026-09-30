import Flapjack.Compiler.Backend.StackProps.ProgramNames
namespace Flapjack.Test.StackPropsProgramNames
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
-- Original HOL inst_good=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.inst (.const 5 0)) := by
  simp [stackAsmName, instName, regName]
-- Original HOL inst_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.inst (.const 6 0)) := by
  simp [stackAsmName, instName, regName]
-- Original HOL heap_alias=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.opCurrHeap .add 1 1) := by
  simp [stackAsmName, regName]
-- Original HOL heap_distinct=F
example (c : AsmConfigExact 8) : ¬ stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.opCurrHeap .add 1 2) := by
  simp [stackAsmName, regName]
-- Original HOL code_good=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.codeBufferWrite 1 5) := by
  simp [stackAsmName, regName]
-- Original HOL code_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.codeBufferWrite 6 1) := by
  simp [stackAsmName, regName]
-- Original HOL data_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.dataBufferWrite 1 6) := by
  simp [stackAsmName, regName]
-- Original HOL seq_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.seq .skip (.ret 6)) := by
  simp [stackAsmName, regName]
-- Original HOL if_ignored=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.ite .equal 99 (.reg 99) .skip .skip) := by
  simp [stackAsmName]
-- Original HOL loop_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.loop (.raise 6)) := by
  simp [stackAsmName, regName]
-- Original HOL raise_good=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.raise 5) := by
  simp [stackAsmName, regName]
-- Original HOL return_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.ret 6) := by
  simp [stackAsmName, regName]
-- Original HOL call_direct=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.call none (.inl 99) none) := by
  simp [stackAsmName]
-- Original HOL call_indirect_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.call none (.inr 6) none) := by
  simp [stackAsmName, regName]
-- Original HOL call_none_handler_ignored=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.call none (.inr 5) (some (.ret 6,3,4))) := by
  simp [stackAsmName, regName]
-- Original HOL call_body_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.call (some (.ret 6,99,1,2)) (.inl 99) none) := by
  simp [stackAsmName, regName]
-- Original HOL call_handler_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.call (some (.skip,99,1,2)) (.inr 5) (some (.raise 6,3,4))) := by
  simp [stackAsmName, regName]
-- Original HOL call_good=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.call (some (.ret 5,99,1,2)) (.inr 5) (some (.raise 5,3,4))) := by
  simp [stackAsmName, regName]
-- Original HOL alloc_default=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1], twoRegArith := true} (.alloc 99) := by
  simp [stackAsmName]
-- Original HOL shared_good=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.shMemOp .load8 1 (.addr 1 0)) := by
  simp [stackAsmName, addrName, regName, asmByteOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL shared_register_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmName {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.shMemOp .load8 6 (.addr 1 0)) := by
  simp [stackAsmName, addrName, regName, asmByteOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL shared_base_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmName {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.shMemOp .load8 1 (.addr 6 0)) := by
  simp [stackAsmName, addrName, regName, asmByteOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL shared_offset_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmName {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.shMemOp .load8 1 (.addr 1 1)) := by
  simp [stackAsmName, addrName, regName, asmByteOffsetOkExact, asmOffsetOkExact, asmAligned]
end Flapjack.Test.StackPropsProgramNames
