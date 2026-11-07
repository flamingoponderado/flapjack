import Flapjack.StackAlloc.Runtime
import Flapjack.RiscV.WordToStack

/-! Regression coverage for constants written to a spilled destination. -/

namespace Flapjack.RiscV

def constSpillValues : Nat → Option (Word 8)
  | 2 => some (BitVec.ofNat 8 23)
  | _ => none

end Flapjack.RiscV
