import Flapjack.Compiler.Encoders.Arm8.Machine.Decode

/-! Concrete round-trip checks for ARMv8 instruction encodings that are not on
the emitted `arm8_ast` path, in particular the `ADRP` (`address true`) field
geometry.  These are kernel `decide` checks, not `native_decide`. -/

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

end Flapjack.Test.Arm8Encoding
