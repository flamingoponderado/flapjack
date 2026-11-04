import Flapjack.RiscV.PipelineDiagnostics

namespace Flapjack.Test.ProductionPreSsaCodec
open Flapjack RiscV WordProgCarrierCodec

/-! Kernel fixtures for actual allocator-input acceptance. These are codec
claims only, not executable parity or HOL simulation tests. -/
private def nested (width : Nat) : LoopProg (BitVec width) :=
  .seq (.primitive [18, 22] .addCarry [2, 4, 6])
    (.loop [2, 4] (.call (some ([18], [22])) (some 100) [2, 4]
      (some (40, .raise 40, .return [18, 22], [2, 4]))) [18, 22])

end Flapjack.Test.ProductionPreSsaCodec
