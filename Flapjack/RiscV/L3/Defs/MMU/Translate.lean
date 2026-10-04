import Flapjack.RiscV.L3.Defs.MMU.Access
namespace Flapjack.RiscV.L3

/-- riscv-mi uses physical addresses exclusively. Unlike HOL, translation cannot
walk page tables, change access bits, populate TLBs or select virtual modes. -/
def translateAddr (arg : BitVec 64 × (fetchType × accessType))
    (state : riscv_state) : Option (BitVec 64) × riscv_state :=
  (some arg.1, state)

end Flapjack.RiscV.L3
