module

public import Flapjack.StackAlloc.Runtime
public import Flapjack.RiscV.WordToStack

@[expose] public section

/-! Regression coverage for shift lowering with two spilled operands. -/

namespace Flapjack.RiscV

def shiftSpillValues : Nat → Option (Word 8)
  | 4 => some (BitVec.ofNat 8 23)
  | _ => none

end Flapjack.RiscV
