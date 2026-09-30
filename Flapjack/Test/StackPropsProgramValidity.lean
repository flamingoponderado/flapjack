import Flapjack.Compiler.Backend.StackProps.ProgramValidity
namespace Flapjack.Test.StackPropsProgramValidity
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
-- Original HOL inst_good=T
example (c : AsmConfigExact 8) : stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.inst (.const 7 0)) := by
  simp [stackAsmOkExact, asmInstOkExact, asmRegOkExact]
-- Original HOL inst_avoided=F
example (c : AsmConfigExact 8) : ¬ stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.inst (.const 0 0)) := by
  simp [stackAsmOkExact, asmInstOkExact, asmRegOkExact]
-- Original HOL inst_bound=F
example (c : AsmConfigExact 8) : ¬ stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.inst (.const 8 0)) := by
  simp [stackAsmOkExact, asmInstOkExact, asmRegOkExact]
-- Original HOL code_good=T
example (c : AsmConfigExact 8) : stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.codeBufferWrite 2 7) := by
  simp [stackAsmOkExact]
-- Original HOL code_avoided=F
example (c : AsmConfigExact 8) : ¬ stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.codeBufferWrite 0 2) := by
  simp [stackAsmOkExact]
-- Original HOL code_bound=F
example (c : AsmConfigExact 8) : ¬ stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.codeBufferWrite 2 8) := by
  simp [stackAsmOkExact]
-- Original HOL data_default=T
example (c : AsmConfigExact 8) : stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.dataBufferWrite 99 99) := by
  simp [stackAsmOkExact]
-- Original HOL heap_default=T
example (c : AsmConfigExact 8) : stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.opCurrHeap .add 99 99) := by
  simp [stackAsmOkExact]
-- Original HOL seq_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.seq .skip (.ret 8)) := by
  simp [stackAsmOkExact]
-- Original HOL if_ignored=T
example (c : AsmConfigExact 8) : stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.ite .equal 99 (.reg 99) .skip .skip) := by
  simp [stackAsmOkExact]
-- Original HOL loop_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.loop (.raise 0)) := by
  simp [stackAsmOkExact]
-- Original HOL raise_good=T
example (c : AsmConfigExact 8) : stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.raise 7) := by
  simp [stackAsmOkExact]
-- Original HOL return_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.ret 8) := by
  simp [stackAsmOkExact]
-- Original HOL call_direct=T
example (c : AsmConfigExact 8) : stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.call none (.inl 99) none) := by
  simp [stackAsmOkExact]
-- Original HOL call_indirect_avoided=F
example (c : AsmConfigExact 8) : ¬ stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.call none (.inr 0) none) := by
  simp [stackAsmOkExact]
-- Original HOL call_indirect_bound=F
example (c : AsmConfigExact 8) : ¬ stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.call none (.inr 8) none) := by
  simp [stackAsmOkExact]
-- Original HOL call_handler_ignored=T
example (c : AsmConfigExact 8) : stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.call none (.inr 7) (some (.ret 8,3,4))) := by
  simp [stackAsmOkExact]
-- Original HOL call_body_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.call (some (.ret 8,99,1,2)) (.inl 99) none) := by
  simp [stackAsmOkExact]
-- Original HOL call_handler_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.call (some (.skip,99,1,2)) (.inr 7) (some (.raise 0,3,4))) := by
  simp [stackAsmOkExact]
-- Original HOL call_good=T
example (c : AsmConfigExact 8) : stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.call (some (.ret 7,99,1,2)) (.inr 7) (some (.raise 2,3,4))) := by
  simp [stackAsmOkExact]
-- Original HOL shared_good=T
example (c : AsmConfigExact 8) : stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.shMemOp .load8 2 (.addr 2 0)) := by
  simp [stackAsmOkExact, asmRegOkExact, asmAddrOkExact, asmByteOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL shared_register_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.shMemOp .load8 0 (.addr 2 0)) := by
  simp [stackAsmOkExact, asmRegOkExact, asmAddrOkExact, asmByteOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL shared_base_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.shMemOp .load8 2 (.addr 0 0)) := by
  simp [stackAsmOkExact, asmRegOkExact, asmAddrOkExact, asmByteOffsetOkExact, asmOffsetOkExact, asmAligned]
-- Original HOL shared_offset_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmOkExact {c with regCount := 8, avoidRegs := [0,1], byteOffset := (0,0)} (.shMemOp .load8 2 (.addr 2 1)) := by
  simp [stackAsmOkExact, asmRegOkExact, asmAddrOkExact, asmByteOffsetOkExact, asmOffsetOkExact, asmAligned]
end Flapjack.Test.StackPropsProgramValidity
