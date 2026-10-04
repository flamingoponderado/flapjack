import Flapjack.RiscV.L3.Defs.MMU.Translate
namespace Flapjack.Test.L3MmuTranslateAddrParity
open Flapjack.RiscV.L3

-- Physical translation is independent of address, access type, core and all
-- retained HOL compatibility configuration, including nonzero VM selectors.
example (address : BitVec 64) (ft : fetchType) (access : accessType)
    (state : riscv_state) :
    translateAddr (address, ft, access) state = (some address, state) := rfl

end Flapjack.Test.L3MmuTranslateAddrParity
