import Flapjack.Pancake.Semantics.PanSem.StateExact
import Flapjack.Test.Fixtures.PanSemExact

/-!
# Sampled original-HOL observations for `panSem$empty_locals`

Reproduces the original-HOL observations in
`scripts/hol-probes/pan_empty_locals_probe.out`: locals are cleared while
`clock` and `globals` are preserved. `PanSemStateExact` uses `MlString` keys,
but its maps are unrestricted lookup functions, so these examples do not
establish equivalence with HOL's finite-map state carrier; the helper and this
test remain untagged.
-/

namespace Flapjack.Test.PanSemEmptyLocalsHOLParity

open Flapjack
open Flapjack.Test.Fixtures.PanSemExact

-- HOL `el_lookup = NONE`: the locals map is cleared.
example : (emptyLocalsHOLExact (width := 64) exactState).locals (ml "x") = none := rfl

-- HOL `el_clock = 5`: the clock is preserved.
example : (emptyLocalsHOLExact (width := 64) exactState).clock = 5 := rfl

-- HOL `el_globals = T`: the globals are preserved.
example :
    (emptyLocalsHOLExact (width := 64) exactState).globals (ml "y")
      = exactState.globals (ml "y") := rfl

/-- A Bool mirror of the three sampled HOL observations. -/
def emptyLocalsGuard : Bool :=
  ((emptyLocalsHOLExact (width := 64) exactState).locals (ml "x")).isNone &&
    (emptyLocalsHOLExact (width := 64) exactState).clock == 5 &&
    ((emptyLocalsHOLExact (width := 64) exactState).globals (ml "y")).isSome

#eval emptyLocalsGuard
#guard emptyLocalsGuard

/-- Runs the parity checks. -/
def runChecks : IO Bool := do
  IO.println "PASS panSem empty_locals function-carrier examples match all 3 HOL observations"
  pure emptyLocalsGuard

end Flapjack.Test.PanSemEmptyLocalsHOLParity
