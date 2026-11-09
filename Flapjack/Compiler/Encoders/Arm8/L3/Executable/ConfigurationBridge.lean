import Flapjack.Compiler.Encoders.Arm8.L3.Configuration
import Flapjack.Compiler.Encoders.Arm8.Configuration
import Flapjack.Compiler.Encoders.Arm8.L3.Executable.BitMask

/-!
# `valid_immediate` on the two carriers

`Arm8.validImmediate` tests the bitwise operators with Flapjack's `Nat`-valued
`encodeBitMask`, while the L3 `arm8ValidImmediate` tests them with the rendered
`EncodeBitMask`.  The two agree because `encodeBitMask_eq` maps the results
elementwise, and `Option.isSome` ignores the mapped payload.

No HOL claim is introduced: the bridge relates two Lean renderings of the same
`valid_immediate` test.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Asm

/-- The two `EncodeBitMask` renderings succeed or fail together. -/
theorem encodeBitMask_isSome_eq (imm : BitVec 64) :
    (encodeBitMask imm).isSome = (EncodeBitMask (TN := 64) imm).isSome := by
  have h := congrArg Option.isSome (encodeBitMask_eq imm)
  simpa only [Option.isSome_map] using h

/-- `validImmediate` equals the L3 `arm8ValidImmediate` on every operator. -/
theorem validImmediate_eq (operator : Sum BinOp Cmp) (i : BitVec 64) :
    Arm8.validImmediate operator i = arm8ValidImmediate operator i := by
  unfold Arm8.validImmediate arm8ValidImmediate
  cases operator with
  | inl bop => cases bop <;> simp [encodeBitMask_isSome_eq]
  | inr cmp => cases cmp <;> simp [encodeBitMask_isSome_eq]

end Flapjack.Compiler.Encoders.Arm8.L3
