import Flapjack.RiscV.L3.Defs.Decode

/-! Regression boundary for the persistent integer-only `riscv-mi` branch.
These are deliberately Flapjack-specific rejection checks, not HOL port claims.
-/
namespace Flapjack.Test.RiscVMiSubset
open Flapjack.RiscV.L3

-- Floating point, atomics, hardware counter reads, paging/status writes,
-- privileged returns, wait-for-interrupt and virtual-memory fences.
private def forbiddenWords : List (BitVec 32) :=
  [0x00000053, 0x00003007, 0x00003027, 0xC0000053,
   0x0000202F, 0x1000202F, 0x1800202F,
   0xC0002073, 0xC0102073, 0xC0202073,
   0x18001073, 0x30001073, 0x10001073,
   0x10000073, 0x10200073, 0x30200073,
   0x30500073, 0x10500073, 0x12000073, 0x0000100F]

#guard forbiddenWords.all (fun word => Decode word == .UnknownInstruction)
#guard DecodeRVC 0x0001 == .UnknownInstruction
#guard DecodeRVC 0x9002 == .UnknownInstruction

-- Integer arithmetic and environment calls remain available.
#guard Decode 0x00100093 == .ArithI (.ADDI (1, 0, 1))
#guard Decode 0x023100B3 == .MulDiv (.MUL (1, 2, 3))
#guard Decode 0x00000073 == .System .ECALL
#guard Decode 0x00100073 == .System .EBREAK

def runChecks : IO Bool := do
  IO.println "PASS riscv-mi rejects floating point, timers, paging and privileged control"
  pure true

end Flapjack.Test.RiscVMiSubset
