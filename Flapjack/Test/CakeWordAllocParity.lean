import Flapjack.RiscV.CakeRegAlloc
import Flapjack.RiscV.LinearScan
import Flapjack.RiscV.LinearScanSource

/-!
# Direct Cake `word_alloc` output parity

The post-SSA two-register add below is copied from
`scripts/hol-probes/word_alloc_add1_probeScript.sml`.  The expected shape is
the checked `word_alloc_add1_probe.out` result from Cake's
`word_allocScript.sml`: the entry move is coloured to `(0,0),(2,2),(4,4)`,
the two source moves retain colours 4 and 2, and the add/return use those
colours.  This exercises the production CakeRegAlloc driver directly rather
than a hand-built allocator state.
-/

namespace Flapjack.Test.CakeWordAllocParity

open Flapjack
open Flapjack.RiscV
open Flapjack.RiscV.CakeRegAlloc

end Flapjack.Test.CakeWordAllocParity
