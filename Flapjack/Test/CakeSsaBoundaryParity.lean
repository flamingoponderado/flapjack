module

public import Flapjack.RiscV.Allocator

@[expose] public section

/-! Direct HOL parity for the Return and Alloc rows of CakeML's
    `full_ssa_cc_trans`.  The expected shapes come from the canonical Cake
    `word_allocScript.sml` equations (`ssa_cc_trans_def`), evaluated with two
    ABI parameters.  This is deliberately separate from the temporary-name,
    branch, and loop fixtures in `CakeSsaTempParity`. -/

namespace Flapjack.Test.CakeSsaBoundaryParity

open Flapjack

end Flapjack.Test.CakeSsaBoundaryParity
