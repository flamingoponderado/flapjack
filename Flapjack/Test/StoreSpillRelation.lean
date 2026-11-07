import Flapjack.StackAlloc.Runtime
import Flapjack.RiscV.WordToStack

/-! Regression coverage for storing through a spilled source. -/

namespace Flapjack.RiscV

def storeSpillValues : Nat → Option (Word 8)
  | 4 => some (BitVec.ofNat 8 23)
  | _ => none

end Flapjack.RiscV
