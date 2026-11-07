import Flapjack.RiscV.CorrectnessColour

/-! Regression for the live-set assignment case of CakeML's
    `evaluate_apply_colour`: a source and destination may share one colour
    when the source is read before the write and no other live value clashes. -/

namespace Flapjack.Test.RiscVColourLivenessParity

open Flapjack.RiscV

private def aliasColour (name : Nat) : Nat := if name = 0 then 0 else 1

private def liveAliasColour (name : Nat) : Nat :=
  if name = 0 then 0 else if name = 3 then 2 else 1

end Flapjack.Test.RiscVColourLivenessParity
