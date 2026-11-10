module

public import Flapjack.StackAlloc.Runtime
public import Flapjack.RiscV.WordToStack

@[expose] public section

/-! Regression coverage for the fully spilled AddCarry lowering. -/

namespace Flapjack.RiscV

def addCarrySpillValues : Nat → Option (Word 8)
  | 5 => some (BitVec.ofNat 8 23)
  | _ => none

end Flapjack.RiscV
