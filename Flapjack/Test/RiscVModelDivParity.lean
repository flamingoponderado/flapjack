import Flapjack.RiscV.Model

/-! Signed-division corner probe for the proof-side RISC-V model.

The proof model's `.divU` instruction is the lowering target of
`wordArithToInstructions` for the signed loop arithmetic `.div`, and
`Flapjack/RiscV/Encoding/NativeInstruction.lean` maps it to the native
`MulDiv .DIV` form (RISC-V signed `DIV`).  The native L3 equation `dfn'DIV`
and HOL `word_quot` both truncate toward zero, so the model must use a
truncating signed quotient (`Int.tdiv` / `BitVec.sdiv`), not a Euclidean one
(`Int.ediv`).  These examples pin the negative-operand corner where the two
roundings disagree: `tdiv (-7) 2 = -3`, whereas `ediv (-7) 2 = -4`. -/
namespace Flapjack.Test.RiscVModelDivParity

open Flapjack.RiscV

/-- A 64-bit state with `x2 = -7` and `x3 = 2`. -/
def divState : State 64 :=
  writeRegister (writeRegister (zeroState 64) 2 (-7 : Word 64)) 3 (2 : Word 64)

example : readRegister (execute divState (.divU 5 2 3)) 5 =
    BitVec.sdiv (-7 : Word 64) (2 : Word 64) := by
  native_decide

example : readRegister (execute divState (.divU 5 2 3)) 5 = -(3 : Word 64) := by
  native_decide

/-- The Euclidean rounding that the model previously used gives a different
result on this corner, documenting the corrected discrepancy. -/
example : BitVec.sdiv (-7 : Word 64) (2 : Word 64) ≠
    BitVec.ofInt 64 ((-7 : Word 64).toInt.ediv (2 : Word 64).toInt) := by
  native_decide

end Flapjack.Test.RiscVModelDivParity
