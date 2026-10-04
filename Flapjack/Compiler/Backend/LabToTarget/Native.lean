import Flapjack.Compiler.Backend.LabSem.State
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabLang
/-- HOL conversion of native assembler/shared-memory/code-buffer instructions. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def cbwToAsmHOL {width : Nat} [NeZero width] :
    AsmOrCbw (HolAsm width) HolMemop (HolAddr width) → HolAsm width
  | .asmi instruction => instruction
  | .cbw left right => .inst (.mem .store8 right (.addr left 0))
  | .shareMem operator register address => .inst (.mem operator register address)
end Flapjack.Compiler.Backend.LabToTarget
