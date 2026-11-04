import Flapjack.RiscV.Allocator

/-! Direct Cake parity for the ordinary Word memory rows of `ssa_cc_trans`.
    These expected forms follow CakeML's `word_allocScript.sml`: Get freshens
    its destination, Store renames both its address expression and value source,
    and Set renames only its expression.  With no incoming SSA bindings,
    `option_lookup` intentionally supplies architectural zero. -/

namespace Flapjack.Test.CakeSsaMemoryParity

open Flapjack

end Flapjack.Test.CakeSsaMemoryParity
