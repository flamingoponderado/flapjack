import Flapjack.Compiler.Backend.WordUnreach
import Flapjack.RiscV.CakeRegAlloc
import Flapjack.Compiler.Backend.WordCse.ListOrder
import Flapjack.Compiler.Backend.WordCse.RegisterUses
import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

namespace Flapjack.Test.ProductionThreeToTwoDomain
open Flapjack Flapjack.RiscV
/-! Kernel regressions for the actual production transform and codec domain.
These are Flapjack-only checks, not original HOL three-to-two output claims.
The production Assign rewrites and nonreturning-handler traversal are tested
as implemented; native pass equality and compiler correctness remain open. -/
end Flapjack.Test.ProductionThreeToTwoDomain
