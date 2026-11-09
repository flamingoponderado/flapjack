module

public import Flapjack.Compiler.Encoders.Asm

@[expose] public section

/-!
# RISC-V unsupported-instruction guard

`riscv_ast_def` maps three instruction shapes to `riscv_encode_fail_def`:
`Inst Skip`, `Arith (LongDiv ...)` and `FP _`.  `Skip` is the assembler's
padding instruction: `lab_to_target` pads sections with it, `enc_line_def`
re-encodes it, and `riscv_encode_fail_def` (`ADDI 0,0,0`) is the intended
four-byte no-op, so a `Skip` line is supported in effect and must not be
rejected.

The other two shapes have no RISC-V lowering: the target configuration has
`has_longdiv = false` and `has_fp_ops = false`, so the compiler never emits
them, and one that appeared would silently receive the no-op encoding instead
of a real instruction.  This module is Flapjack-only driver infrastructure: it
names those two shapes so the driver can reject them with a located error
before encoding.  There is no separately named HOL declaration for this guard.
-/

namespace Flapjack.Compiler.Encoders.RiscV

open Flapjack.Compiler.Encoders.Asm

/-- A shape `riscvAst` lowers to `riscvEncodeFail` and that the RISC-V
configuration never emits. -/
inductive UnsupportedReason where
  | longDiv
  | fp
  deriving DecidableEq, Repr

/-- Human-readable description of an unsupported RISC-V instruction shape. -/
def unsupportedReasonDescription : UnsupportedReason → String
  | .longDiv =>
      "LongDiv has no RISC-V encoding (the encoder emits the fail encoding)"
  | .fp =>
      "a floating-point instruction has no RISC-V encoding " ++
        "(the encoder emits the fail encoding)"

/-- The two fail shapes the RISC-V configuration never emits, if any.  `Skip`
is excluded: its fail encoding is the intended padding no-op. -/
def riscvUnsupported : HolAsm 64 → Option UnsupportedReason
  | .inst (.arith (.longDiv _ _ _ _ _)) => some .longDiv
  | .inst (.fp _) => some .fp
  | _ => none

end Flapjack.Compiler.Encoders.RiscV
