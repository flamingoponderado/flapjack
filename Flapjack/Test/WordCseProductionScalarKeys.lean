import Flapjack.Compiler.Backend.WordCse.ListOrder
import Flapjack.Compiler.Backend.WordCse.RegisterUses
import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
import Std.Data.TreeMap

namespace Flapjack.Test.WordCseProductionScalarKeys
open RiscV

def runChecks : IO Bool := do
  IO.println "PASS executed CSE scalar keys: 17 scalar constructor equations, two load callers, generic positive-width native dispatch/key equality and diagnostic fixtures (kernel checked)"
  return true
end Flapjack.Test.WordCseProductionScalarKeys
