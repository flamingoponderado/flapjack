import Flapjack.Compiler.Encoders.RiscV.Target.Configuration

/-! Generated original `riscv_targetScript.sml` assembler rewrite bundles.

`asmLib.target_asm_rwts [] ``riscv_config``` (riscv_targetScript.sml:331/333)
emits the two rewrite theorems `riscv_config` and `riscv_asm_ok`, which
`riscv_targetProofScript.sml` uses as `simp` lemmas (lines 196, 199, 322, 481,
517).  The first enumerates every field of the source `riscv_config` record; the
second expands `asm_ok ... riscv_config` for each assembler form. -/
namespace Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack Compiler.Encoders.Asm

/-- Generated HOL `riscv_config` (riscv_targetScript.sml:331): the full source
field bundle of `riscv_config`, in original order and with the original signed
`valid_imm`/offset endpoints. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem riscvConfigRewrites :
    riscvConfig.isa = .riscv ∧
    riscvConfig.encode = riscvEnc ∧
    riscvConfig.bigEndian = false ∧
    riscvConfig.codeAlignment = 2 ∧
    riscvConfig.linkReg = some 1 ∧
    riscvConfig.avoidRegs = [0, 2, 3, 4, 31] ∧
    riscvConfig.regCount = 32 ∧
    riscvConfig.fpRegCount = 0 ∧
    riscvConfig.twoRegArith = false ∧
    riscvConfig.validImm =
      (fun operator i =>
        (match operator with
         | .inl .sub => (-2048 : BitVec 64).slt i
         | _ => (-2048 : BitVec 64).sle i) && i.sle 2047) ∧
    riscvConfig.addrOffset = (-2048, 2047) ∧
    riscvConfig.hwOffset = (-2048, 2047) ∧
    riscvConfig.byteOffset = (-2048, 2047) ∧
    riscvConfig.jumpOffset = (-2147483648, 0x7FFFF7FF) ∧
    riscvConfig.cjumpOffset = (-1048568, 1048579) ∧
    riscvConfig.locOffset = (-2147483648, 0x7FFFF7FF) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

end Flapjack.Compiler.Encoders.RiscV.Target
