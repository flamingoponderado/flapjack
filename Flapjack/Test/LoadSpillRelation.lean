import Flapjack.StackAlloc.Runtime
import Flapjack.RiscV.WordToStack

/-! Regression coverage for loading through a spilled address. -/

namespace Flapjack.RiscV

def loadSpillValues : Nat → Option (Word 8)
  | 3 => some (BitVec.ofNat 8 23)
  | _ => none

end Flapjack.RiscV
