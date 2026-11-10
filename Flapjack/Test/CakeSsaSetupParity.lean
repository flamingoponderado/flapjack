module

public import Flapjack.RiscV.CakeAllocatorCore
public import Flapjack.RiscV.CakeSsaSetup

@[expose] public section

/-! Direct HOL parity for CakeML `total_colour` and `setup_ssa`.
    Fixtures are in `scripts/hol-probes/word_alloc_setup_colour_probe.out`. -/

namespace Flapjack.Test.CakeSsaSetupParity

open Flapjack
open Flapjack.RiscV.CakeAlloc
open Flapjack.RiscV.CakeRegAlloc

end Flapjack.Test.CakeSsaSetupParity
