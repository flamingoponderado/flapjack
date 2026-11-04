import Flapjack.RiscV.Allocator

/-! Direct Cake parity for ordinary `ssa_cc_trans_inst` rows from
    `cakeml/compiler/backend/word_allocScript.sml:137-230`.  The exact shapes
    below come from the canonical HOL `full_ssa_cc_trans` probe
    `cake_inst_probeScript.sml`: ordinary arithmetic reads the SSA sources,
    while loads freshen the destination and stores preserve the source names. -/

namespace Flapjack.Test.CakeSsaInstParity

open Flapjack

end Flapjack.Test.CakeSsaInstParity
