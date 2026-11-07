import Flapjack.RiscV.WordToStack
import Flapjack.Compiler.Backend.WordCse.ListOrder
import Flapjack.Compiler.Backend.WordCse.RegisterUses
import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
import Std.Data.TreeMap
import Flapjack.RiscV.Backend
import Flapjack.RiscV.Encoding

/-! Matching executed observations of the original overflow constructors.
The full original HOL results live in word_overflow_production_probe.out.
These are carrier/consumer fixtures, not a full pass simulation theorem. -/
namespace Flapjack.Test.WordOverflowProduction
open Flapjack Flapjack.RiscV

end Flapjack.Test.WordOverflowProduction
