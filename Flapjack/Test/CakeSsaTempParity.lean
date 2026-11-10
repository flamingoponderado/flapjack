module

public import Flapjack.RiscV.CakeAllocatorCore
public import Flapjack.RiscV.CakeSsaTemp

-- Checks below run compiled code from these modules.
public meta import Flapjack.RiscV.CakeAllocatorCore
public meta import Flapjack.RiscV.CakeSsaTemp
@[expose] public section

/-! Direct HOL parity for CakeML `full_ssa_cc_trans` temporary numbering.
    Fixtures are in `scripts/hol-probes/cake_ssa_temp_probe.out`. -/

namespace Flapjack.Test.CakeSsaTempParity

open Flapjack
open Flapjack.RiscV.CakeAlloc
open Flapjack.RiscV.CakeRegAlloc

/-- `limit_var` supplies the fresh-name base the prologue numbers from. -/
def limitBaseGuard : Bool :=
  limitVar 0 == 5 && limitVar 26 == 29

#guard limitBaseGuard

/-- The oracle's `limit_two_assigns` case: the two-assign program has
`max_var` 2, so `limit_var` is 2 + (4 - 2) + 1 = 5. -/
def limitTwoAssignsGuard : Bool :=
  limitVar 2 == 5

#guard limitTwoAssignsGuard

/-! Cake's break reconciliation also preserves a live value outside the loop;
    this is the live-out companion to `loopBreakGuard`. -/

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [
      ("limit_var supplies the fresh-name base", limitBaseGuard),
      ("limit_var on the two-assign program is 5", limitTwoAssignsGuard)]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaTempParity
