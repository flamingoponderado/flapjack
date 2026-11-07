import Flapjack.StackAlloc.Runtime
import Flapjack.RiscV.WordToStack

/-! Regression coverage for public arithmetic division with spilled operands. -/

namespace Flapjack.RiscV

def directDivValues : Nat → Option (Word 8)
  | 4 => some (BitVec.ofNat 8 23)
  | _ => none

end Flapjack.RiscV
