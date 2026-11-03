import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ShiftBitfield

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# Mask algebra for the `BitfieldMove@64` shift-immediate forms

`DecodeBitMasks` at the shapes `arm8_ast` emits for `Shift` with an immediate,
together with the mask identities of `arm8_targetProofScript.sml`'s `lsl`,
`lsr` and `asr2`.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- `DecodeBitMasks` at the `Lsr`/`Asr` shape `(1, 63w, n2w n, F)`; the two
masks are the all-ones word and the "keep the low `64 - n` bits" word. -/
theorem decodeBitMasks_lsr (n : Nat) (hn : n < 64) :
    DecodeBitMasks (TM := 64)
      ((1 : BitVec 1), (BitVec.ofNat 6 63, (BitVec.ofNat 6 n, false))) =
      some (Replicate (holRotate (holPadLeft false 64 (Ones 64)) n),
        Replicate (holPadLeft false 64 (Ones (63 - n + 1)))) := by
  interval_cases n <;> decide

end Flapjack.Compiler.Encoders.Arm8.L3
