import Flapjack.RiscV.Allocator

/-! Direct Cake parity for the remaining memory-shaped `ssa_cc_trans` rows.
    The expected forms are the source equations in CakeML's
    `word_allocScript.sml`: `OpCurrHeap` renames its destination while reading
    the source, `ShareInst` loads freshen their destination, and stores retain
    the source read.  Address expressions are renamed before that distinction.
    These cases are separate from the ABI/control boundary guards because they
    feed the backend's shared-memory and current-heap instruction paths. -/

namespace Flapjack.Test.CakeSsaSharedParity

open Flapjack

end Flapjack.Test.CakeSsaSharedParity
