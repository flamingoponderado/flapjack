module

public import Flapjack.Pancake.LoopToWord.CompFuncExact
public import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
public import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

@[expose] public section

namespace Flapjack.Test.LoopToWordSourceCodec
open Flapjack

/-! Kernel fixtures for full source-output codec closure. These test the real
routed compiler and rejection distinction, not HOL execution equivalence. -/

private def nested (width : Nat) : LoopProg (BitVec width) :=
  .seq (.primitive [18, 22] .addCarry [2, 4, 6])
    (.loop [2, 4] (.call (some ([18], [22])) (some 100) [2, 4]
      (some (40, .raise 40, .return [18, 22], [2, 4]))) [18, 22])

end Flapjack.Test.LoopToWordSourceCodec
