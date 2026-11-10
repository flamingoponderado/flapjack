module

public import Flapjack.RiscV.WordExpressionFlatten

@[expose] public section

namespace Flapjack.RiscV

/-! Independent Cake `inst_select_def` Store oracle for the unresolved
    selector/allocator carrier boundary.  These are the exact Word shapes
    from `cakeml/compiler/backend/word_instScript.sml:389-401`; they are kept
    separate from `wordInstSelectProgram` because the current source-shaped
    pipeline intentionally preserves the baseline artifacts while the
    downstream carrier integration is still being repaired. -/
end Flapjack.RiscV
