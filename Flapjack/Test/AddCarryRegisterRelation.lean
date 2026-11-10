module

public import Flapjack.StackAlloc.Runtime
public import Flapjack.RiscV.WordToStack

@[expose] public section

/-! Regression coverage for register-resident AddCarry lowering. -/

namespace Flapjack.RiscV

def addCarryRegisterValues : Nat → Option (Word 8) := fun name =>
  if name = 5 then some (BitVec.ofNat 8 23) else none

end Flapjack.RiscV
