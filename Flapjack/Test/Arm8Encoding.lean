import Flapjack.Compiler.Encoders.Arm8.Machine.Decode
import Flapjack.Compiler.Encoders.Arm8.Machine.Execute

/-! Concrete round-trip checks for ARMv8 instruction encodings that are not on
the emitted `arm8_ast` path, in particular the `ADRP` (`address true`) field
geometry.  These are kernel-checked by `decide` or `simp`, with no native
decision procedure. -/

namespace Flapjack.Test.Arm8Encoding
open Flapjack.Compiler.Encoders.Arm8

theorem adrp_roundtrip_positive :
    decodeInsn ((encodeInsn (.address true 0x12345000 0)).getD 0) =
      some (.address true 0x12345000 0) := by decide

theorem adrp_roundtrip_negative :
    decodeInsn ((encodeInsn (.address true 0xFFFFFFFFFFFFF000 0)).getD 0) =
      some (.address true 0xFFFFFFFFFFFFF000 0) := by decide

theorem adrp_roundtrip_bit32 :
    decodeInsn ((encodeInsn (.address true 0xFFFFFFFF00000000 0)).getD 0) =
      some (.address true 0xFFFFFFFF00000000 0) := by decide

theorem adrp_rejects_too_large :
    encodeInsn (.address true 0x100000000 0) = none := by decide

theorem adr_roundtrip_not_multiple_of_four :
    decodeInsn ((encodeInsn (.address false 0x7FFFF 0)).getD 0) =
      some (.address false 0x7FFFF 0) := by decide

theorem adrp_roundtrip_nonzero_rd :
    decodeInsn ((encodeInsn (.address true 0x12345000 7)).getD 0) =
      some (.address true 0x12345000 7) := by decide

theorem adrp_rejects_unaligned :
    encodeInsn (.address true 0x12345001 0) = none := by decide

/-- `pc = 0x1000` makes `pc - 4 = 0xFFC` fall on page 0, so this distinguishes
the page-base computation from dropping the `-4`, using `pc`, or omitting the
page mask. -/
theorem adrp_exec_page_offset :
    let s : Arm8State :=
      { regs := fun _ => 0, pc := 0x1000, n := false, z := false, c := false, v := false,
        mem := fun _ => 0, memDomain := fun _ => True, failed := false }
    readReg (execInsn s (.address true 0x12345000 7)) 7 = 0x12345000 := by
  simp [execInsn, writeReg, readReg]

end Flapjack.Test.Arm8Encoding
