import Flapjack.StackAlloc.Runtime
import Flapjack.RiscV.WordToStack

/-! Regression coverage for Set with a spilled source. -/

namespace Flapjack.RiscV

def setSpillValues : Nat → Option (Word 8)
  | 3 => some (BitVec.ofNat 8 23)
  | _ => none

end Flapjack.RiscV
