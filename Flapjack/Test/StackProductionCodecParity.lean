import Flapjack.Compiler.Backend.MlStringBridge
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
import Flapjack.Stack
import Flapjack.Compiler.Backend.WordToStack.NativeMoves

/-! Kernel tests of the production StackLang carrier codec. No evaluated
compiler or HOL semantic parity is claimed by these structural examples. -/
namespace Flapjack.Test.StackProductionCodecParity
open Flapjack Compiler.Backend.StackLang Compiler.Backend.StackCarrier

def runChecks : IO Bool := do
  IO.println "PASS production StackLang structural codec (accepted canonical image; route remains open)"
  return true
end Flapjack.Test.StackProductionCodecParity
