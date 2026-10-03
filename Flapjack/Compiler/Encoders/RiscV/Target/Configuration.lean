import Flapjack.Compiler.Encoders.RiscV.Target

/-! Full original native RISC-V assembler configuration. All fields use the
accepted exact ASM carrier; encode is the complete native byte encoder.
The separate production-routing bead remains open. -/
namespace Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack Compiler.Encoders.Asm

/-- Complete source record at fixed word64, including its real encode field.
Signed word comparisons preserve the strict Sub lower bound and every original
range endpoint. The generic legacy check record remains separate and untagged. -/
@[hol "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_config_def"]
def riscvConfig : AsmConfigExact 64 where
  isa := .riscv
  encode := riscvEnc
  regCount := 32
  avoidRegs := [0,2,3,4,31]
  fpRegCount := 0
  linkReg := some 1
  twoRegArith := false
  bigEndian := false
  validImm := fun operator i =>
    (match operator with
     | .inl .sub => (-2048 : BitVec 64).slt i
     | _ => (-2048 : BitVec 64).sle i) && i.sle 2047
  addrOffset := (-2048,2047)
  hwOffset := (-2048,2047)
  byteOffset := (-2048,2047)
  jumpOffset := (-2147483648,0x7FFFF7FF)
  cjumpOffset := (-1048576+8,1048575+4)
  locOffset := (-2147483648,0x7FFFF7FF)
  codeAlignment := 2

/-- Derived projection of the whole source record; there is no separately
named HOL theorem for this definitional field equality. -/
theorem riscvConfig_encode : riscvConfig.encode = riscvEnc := rfl
end Flapjack.Compiler.Encoders.RiscV.Target
