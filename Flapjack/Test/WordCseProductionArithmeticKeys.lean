import Flapjack.Compiler.Backend.WordCse.ListOrder
import Flapjack.Compiler.Backend.WordCse.RegisterUses
import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
import Std.Data.TreeMap

/-! Same-input original instruction-key observations at the actual executed
CSE call sites. Overflow and FP native rows have no production carrier and are
outside this routing slice; the five-register extension is explicitly separate. -/
namespace Flapjack.Test.WordCseProductionArithmeticKeys
open Flapjack Flapjack.RiscV

end Flapjack.Test.WordCseProductionArithmeticKeys
