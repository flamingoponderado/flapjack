module

public import Flapjack.StackAlloc.Runtime
public import Flapjack.RiscV.WordToStack

@[expose] public section

/-! Regression coverage for a StackStore lookup into a spilled destination. -/

namespace Flapjack.RiscV

def lookupSpillValues : Nat → Option (Word 8)
  | 2 => some (BitVec.ofNat 8 23)
  | _ => none

end Flapjack.RiscV
