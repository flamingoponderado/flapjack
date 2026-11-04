import Flapjack.StackAlloc.Runtime
import Flapjack.RiscV.WordToStack

/-! Regression coverage for the fully spilled LongMul lowering. -/

namespace Flapjack.RiscV

def longMulSpillValues : Nat → Option (Word 8) := fun name =>
  if name = 4 then some (BitVec.ofNat 8 23) else none

end Flapjack.RiscV
