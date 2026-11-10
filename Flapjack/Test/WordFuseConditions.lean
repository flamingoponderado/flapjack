module

public import Flapjack.RiscV.WordFuseConditions

@[expose] public section

open Flapjack Flapjack.RiscV

namespace Flapjack.Test.WordFuseConditions

/-! The source pipeline can leave harmless `Skip` wrappers around the branch
    definitions and between the copy and the test.  Cake's `Seq_assoc` removes
    those wrappers before this rewrite; keep this shape covered as well. -/
end Flapjack.Test.WordFuseConditions
