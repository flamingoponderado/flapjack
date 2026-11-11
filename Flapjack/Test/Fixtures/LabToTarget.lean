module

public import Flapjack.Compiler.Encoders.Asm

@[expose] public section

/-!
# Shared LabToTarget oracle fixture

The `AsmConfigExact 64` configuration used by the lab-to-target parity rows in
`Flapjack/Test/LabToTargetCompileParity.lean`, `Flapjack/Test/LabToTargetPaddingParity.lean`
and `Flapjack/Test/LabToTargetRemoveLabelsParity.lean`. The probes run with the
RISC-V ISA and every offset range wide enough not to reject the fixtures.
-/

namespace Flapjack.Test.Fixtures.LabToTarget

open Flapjack
open Flapjack.Compiler.Encoders.Asm

/-- The RISC-V assembly configuration shared by the lab-to-target parity rows. -/
def cfg : AsmConfigExact 64 :=
  { isa := .riscv
    encode := fun _ => []
    bigEndian := false
    codeAlignment := 2
    linkReg := none
    avoidRegs := [3]
    regCount := 8
    fpRegCount := 4
    twoRegArith := true
    validImm := fun _ _ => true
    addrOffset := (0, 100)
    hwOffset := (0, 100)
    byteOffset := (0, 100)
    jumpOffset := (0, 100)
    cjumpOffset := (0, 100)
    locOffset := (0, 100) }

/-- The RISC-V 8-bit assembly configuration shared by the lab-validity rows. -/
def cfg8 : AsmConfigExact 8 :=
  { isa := .riscv
    encode := fun _ => []
    bigEndian := false
    codeAlignment := 2
    linkReg := none
    avoidRegs := [3]
    regCount := 8
    fpRegCount := 4
    twoRegArith := true
    validImm := fun _ _ => true
    addrOffset := (0,100)
    hwOffset := (0,100)
    byteOffset := (0,100)
    jumpOffset := (0,100)
    cjumpOffset := (0,100)
    locOffset := (0,100) }

end Flapjack.Test.Fixtures.LabToTarget
