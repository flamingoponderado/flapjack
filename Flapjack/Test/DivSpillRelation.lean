import Flapjack.StackAlloc.Runtime
import Flapjack.RiscV.WordToStack

/-! Regression coverage for division with a fully spilled operand triple. -/

namespace Flapjack.RiscV

def divSpillValues : Nat → Option (Word 8)
  | 4 => some (BitVec.ofNat 8 23)
  | _ => none

end Flapjack.RiscV
