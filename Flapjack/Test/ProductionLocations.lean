import Flapjack.RiscV.CakeRegAlloc
import Flapjack.Compiler.Backend.WordToStackRegFormat
import Flapjack.Compiler.Backend.WordUnreach
import Flapjack.Compiler.Backend.WordCse.ListOrder
import Flapjack.Compiler.Backend.WordCse.RegisterUses
import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec

namespace Flapjack.Test.ProductionLocations
open Flapjack RiscV RiscV.CakeRegAlloc

/-! Kernel fixtures for actual operand locations. No HOL simulation or
executed lowering equivalence is asserted by these tests. -/
end Flapjack.Test.ProductionLocations
