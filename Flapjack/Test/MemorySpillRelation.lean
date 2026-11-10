module

public import Flapjack.StackAlloc.Runtime
public import Flapjack.RiscV.WordToStack

@[expose] public section

/-! Regression coverage for direct memory load/store spill lowering. -/

namespace Flapjack.RiscV

def memorySpillValues : Nat → Option (Word 8)
  | 3 => some (BitVec.ofNat 8 23)
  | _ => none

end Flapjack.RiscV
