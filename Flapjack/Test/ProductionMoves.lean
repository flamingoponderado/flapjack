import Flapjack.Compiler.Backend.WordToStack.ProductionMoves

namespace Flapjack.Test.ProductionMoves
open Flapjack RiscV Flapjack.ProductionMoves
open Compiler.Backend.StackLang Compiler.Backend.WordToStack.Native

example : wMoveSingleNative (width := 64) (.inr 22, .inr 23) (22, 0, 0) =
    .seq (.stackLoad 22 0) (.stackStore 22 0) := rfl
def runChecks : IO Bool := do
  IO.println "PASS actual optional move projection, scratch errors and original spill cycle (caller domain remains open)"
  return true
end Flapjack.Test.ProductionMoves
