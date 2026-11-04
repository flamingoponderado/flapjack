import Flapjack.StackAlloc.Runtime
import Flapjack.RiscV.WordToStack

/-! Regression coverage for mixed register/stack move preservation. -/

namespace Flapjack.RiscV

def spillMoveValues : Nat → Option (Word 8)
  | 3 => some (BitVec.ofNat 8 17)
  | _ => none

end Flapjack.RiscV
