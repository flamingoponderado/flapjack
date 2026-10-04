import Flapjack.Compiler.Backend.LabToTarget.Labels

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Original annotated length: deliberately independent of encoded byte length. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def lineLen {width : Nat} [NeZero width] :
    Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width) → Nat
  | .label _ _ len => len
  | .asm _ _ len => len
  | .labAsm _ _ _ len => len

end Flapjack.Compiler.Backend.LabToTarget
