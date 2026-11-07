import Flapjack.Pancake.WordLang

/-! Focused width-indexed executable/exact Word expression carrier fixtures. -/

namespace Flapjack.Test.WordExpCarrierCodecParity

open Flapjack

def exactNested : WordLangExpHOL (BitVec 8) :=
  .op .add
    [.const 7, .load (.var 3), .lookup (.temp (BitVec.ofNat 5 9)),
      .shift .lsl (.var 5) (.const 1)]

end Flapjack.Test.WordExpCarrierCodecParity
