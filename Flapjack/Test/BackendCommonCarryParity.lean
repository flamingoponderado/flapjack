module

public import Flapjack.Compiler.Backend.BackendCommon
public import Flapjack.Compiler.Backend.BackendCommon.UpperW2w

-- Checks below run compiled code from these modules.
public meta import Flapjack.Compiler.Backend.BackendCommon
public meta import Flapjack.Compiler.Backend.BackendCommon.UpperW2w
public meta import Flapjack.Pancake.Semantics.PanSem
@[expose] public section

namespace Flapjack.Test.BackendCommonCarryParity

open Flapjack

/-! Exact numeric outputs from `word_add_carry_probe.out`, produced by the
    original CakeML `backend_common$word_add_carry` on 8-bit words. -/
def carryOutput (left right carry : BitVec 8) : Nat × Nat :=
  let (result, overflow) := wordAddCarryHOL left right carry
  (result.toNat, overflow.toNat)

#guard carryOutput 3 4 0 == (7, 0)
#guard carryOutput 255 1 0 == (0, 1)
#guard carryOutput 3 4 2 == (8, 0)
#guard carryOutput 255 0 1 == (0, 1)

-- The original upper-word conversion puts 32-bit inputs in the high half.
#guard upperW2w (0x89abcdef : BitVec 32) == (0x89abcdef00000000 : BitVec 64)
#guard upperW2w (0x89abcdef : BitVec 64) == (0x89abcdef : BitVec 64)
#guard upperW2w (0xab : BitVec 8) == (0xab : BitVec 64)

end Flapjack.Test.BackendCommonCarryParity
