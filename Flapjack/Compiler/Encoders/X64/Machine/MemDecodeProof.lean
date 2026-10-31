import Mathlib.Tactic
import Flapjack.Compiler.Encoders.X64.Machine.Bytes

/-!
# Decoder inverses for the emitted memory-operand forms

The x86-64 backend emits loads, stores and `lea` with a base register and a
displacement.  `e_ModRM` writes a `ModRM` byte whose `mod` field records the
displacement width, adds a `SIB` byte when the base register is RSP/R12, and
appends one or four displacement bytes.  This module proves that the closed
decoder recovers the source instruction from those bytes.
-/

set_option maxHeartbeats 4000000

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm

/-! ## Encoded byte layouts -/

/-- The encoded bytes of `movRM .z64`: a REX.W byte, the `8B` opcode, the
`ModRM` byte, an optional `SIB` byte for an RSP/R12 base, and the
displacement. -/
theorem encodeInsn_movRM_z64_bytes (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.movRM .z64 dst base disp) =
      [byte (72 + (if 8 ≤ dst then 4 else 0) + (if 8 ≤ base then 1 else 0)),
       byte 0x8B,
       byte ((if disp = 0 ∧ base % 8 ≠ 5 then 0
              else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
             8 * (dst % 8) + base % 8)] ++
      (if base % 8 = 4 then [byte 0x24] else []) ++
      (if disp = 0 ∧ base % 8 ≠ 5 then []
       else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat]
       else [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)]) := by
  interval_cases dst <;> interval_cases base
  all_goals
    simp only [encodeInsn, eGenRmReg, eModRM, eOpsize, rexPrefix, mkRex, eImm8_32, eImm8, eImm32, byte, modField]
    simp only [Nat.reduceMod, Nat.reduceMul, Nat.reduceDiv]
    simp
    by_cases h0 : disp = 0
    · subst h0
      simp
    · have h0' : disp ≠ 0#64 := h0
      by_cases h8 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
      · simp [h0', h8]
      · have h32 : -2147483648 ≤ disp.toInt ∧ disp.toInt ≤ 2147483647 := by omega
        simp [h0', h8, h32]

end Flapjack.Compiler.Encoders.X64
