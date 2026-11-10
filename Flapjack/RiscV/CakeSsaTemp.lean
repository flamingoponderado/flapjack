module

public import Flapjack.RiscV.CakeSsaSetup

@[expose] public section

/-! Source-shaped temporary-numbering boundary for CakeML's
`full_ssa_cc_trans` (cakeml/compiler/backend/word_allocScript.sml:1822).

The original computes `lim = limit_var prog` and then runs
`setup_ssa n lim prog`, which becomes the `Move1` prologue renamed onto the
fresh temporary names.  The composed prologue is the part of the numbering
that matters at the frame boundary; the SSA/CC body renaming is separate.
The oracle values live in `scripts/hol-probes/cake_ssa_temp_probe.out`. -/

namespace Flapjack.RiscV.CakeRegAlloc

open Flapjack

end Flapjack.RiscV.CakeRegAlloc