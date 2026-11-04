import Flapjack.Pancake.LoopLang

/-! Focused constructor and rejection fixtures for the width-indexed
executable/exact Loop expression codec. -/

namespace Flapjack.Test.LoopToWordExpCarrierCodecParity

open Flapjack

def nestedExact : HolLoopExp 8 :=
  .op .add [.const 7, .load (.var 3), .shift .lsl (.var 5) (.const 1)]

end Flapjack.Test.LoopToWordExpCarrierCodecParity
