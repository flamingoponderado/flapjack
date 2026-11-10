module

public import Flapjack.Compiler.Backend.LabProps

-- Checks below run compiled code from these modules.
public meta import Flapjack.Parser.Basic
public meta import Flapjack.LoopGetVarImm
public meta import Flapjack.Pancake.WordLang
public meta import Flapjack.Compiler.Encoders.Asm
public meta import Flapjack.Compiler.Backend.LabProps
@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# RISC-V assembler configuration parity

Checks the check-relevant `riscvConfigForChecks` field values against the direct HOL
oracle `scripts/hol-probes/riscv_config_probe.out` (HOL `riscv_config_def`,
`cakeml/compiler/encoders/riscv/riscv_targetScript.sml:277-304`).  `encode`
is the documented placeholder and is not read by any validity predicate.
-/

namespace Flapjack.Test.RiscvConfigParity

open Flapjack
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackProps

private def isaIsRiscv (config : AsmConfig width) : Bool :=
  match config.isa with
  | .riscv => true
  | _ => false

private def linkRegOne (config : AsmConfig width) : Bool :=
  match config.linkReg with
  | some 1 => true
  | _ => false

private def w64 (n : Int) : BitVec 64 := BitVec.ofInt 64 n

/-- All 19 oracle rows of `riscv_config_probe.out`. -/
def riscvConfigForChecksGuard : Bool :=
  isaIsRiscv riscvConfigForChecks &&
  (riscvConfigForChecks.regCount == 32) &&
  (riscvConfigForChecks.avoidRegs == [0, 2, 3, 4, 31]) &&
  (riscvConfigForChecks.fpRegCount == 0) &&
  linkRegOne riscvConfigForChecks &&
  (riscvConfigForChecks.twoRegArith == false) &&
  (riscvConfigForChecks.bigEndian == false) &&
  (riscvConfigForChecks.codeAlignment == 2) &&
  (riscvConfigForChecks.addrOffset == (riscvMin12, riscvMax12)) &&
  (riscvConfigForChecks.hwOffset == (riscvMin12, riscvMax12)) &&
  (riscvConfigForChecks.byteOffset == (riscvMin12, riscvMax12)) &&
  (riscvConfigForChecks.jumpOffset == (riscvMin32, riscvJumpMax)) &&
  (riscvConfigForChecks.cjumpOffset == (riscvMin21 + 8, riscvMax21 + 4)) &&
  (riscvConfigForChecks.locOffset == (riscvMin32, riscvJumpMax)) &&
  (riscvConfigForChecks.validImm (.inl .sub) (w64 (-2048)) == false) &&
  (riscvConfigForChecks.validImm (.inl .sub) (w64 (-2047)) == true) &&
  (riscvConfigForChecks.validImm (.inl .add) (w64 (-2048)) == true) &&
  (riscvConfigForChecks.validImm (.inl .add) (w64 2047) == true) &&
  (riscvConfigForChecks.validImm (.inl .add) (w64 2048) == false)

#guard riscvConfigForChecksGuard

-- The config drives the StackProps instruction checks.
private def riscvChecks := asmChecksOfConfig riscvConfigForChecks

#guard riscvChecks.instOk (.skip : WordLangInst (BitVec 64)) == true
#guard riscvChecks.regOk 1 == true
#guard riscvChecks.regOk 0 == false
#guard riscvChecks.regOk 31 == false

def runChecks : IO Bool := do
  if riscvConfigForChecksGuard then
    IO.println "PASS riscv_config fields match the HOL oracle"
  else
    IO.println "FAIL riscv_config fields match the HOL oracle"
  pure riscvConfigForChecksGuard

end Flapjack.Test.RiscvConfigParity