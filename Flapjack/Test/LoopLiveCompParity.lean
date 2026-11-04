import Flapjack.Pancake.LoopLive

namespace Flapjack.Test.LoopLiveCompParity

/-! Direct parity for `loop_live$comp` (`loop_liveScript.sml:217`); these
observations replay `scripts/hol-probes/loop_live_comp_probe.out`. -/
def largeLiveInFuelMatchesCake : Bool :=
  loopFixedpointFuel (List.range 65) == 66

#guard largeLiveInFuelMatchesCake

end Flapjack.Test.LoopLiveCompParity
