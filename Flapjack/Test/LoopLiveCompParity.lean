module

public import Flapjack.Pancake.LoopLive

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.LoopLang
public meta import Flapjack.Pancake.LoopLive
@[expose] public section

namespace Flapjack.Test.LoopLiveCompParity

/-! Direct parity for `loop_live$comp` (`loop_liveScript.sml:217`); these
observations replay `scripts/hol-probes/loop_live_comp_probe.out`. -/
def largeLiveInFuelMatchesCake : Bool :=
  loopFixedpointFuel (List.range 65) == 66

#guard largeLiveInFuelMatchesCake

end Flapjack.Test.LoopLiveCompParity
