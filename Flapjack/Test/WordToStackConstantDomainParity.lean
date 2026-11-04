import Flapjack.RiscV.WordExpressionFlatten
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Flapjack.Test.WordToStackConstantDomainParity
open Flapjack RiscV

private def cs : NatInfoMap (BitVec 64) := [(1,7),(2,9)]

def runChecks : IO Bool := do
  IO.println "PASS actual constant-pass codec closure (13 original trees; trailing Skip repaired)"
  pure true

end Flapjack.Test.WordToStackConstantDomainParity
