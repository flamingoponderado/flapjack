import Flapjack.StackAlloc.Runtime
import Flapjack.RiscV.WordToStack

/-! Regression coverage for mixed-source spilled-destination LongMul. -/

namespace Flapjack.RiscV

def longMulMixedValues : Nat → Option (Word 8) := fun name =>
  if name = 4 then some (BitVec.ofNat 8 23) else none

end Flapjack.RiscV
