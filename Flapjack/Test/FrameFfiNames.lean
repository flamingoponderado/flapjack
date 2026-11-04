import Flapjack.RiscV.LabToTargetRoute

namespace Flapjack.Test.FrameFfiNames

open Flapjack.RiscV Flapjack.Compiler.Backend

private def external (name : String) : HolFfiName :=
  .extCall (Basis.Pure.MlString.ofString name)

end Flapjack.Test.FrameFfiNames
