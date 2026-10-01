import Flapjack.Compiler.Backend.Parmove.PmovMapInj

namespace Flapjack.Test.ParmovePmovMapInjParity
open Compiler.Backend.Parmove

/-! Kernel checks for the literal HOL theorem `pmov_MAP_INJ`
(`parmoveScript.sml:1257`): the deterministic scheduler `pmov` commutes with
`map_state f` for a renaming injective on a well-formed state. -/

-- The scheduler commutes with `map_state` under the original well-formedness
-- and source injectivity premises.
example {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : Option α → Option β) (state : State α)
    (valid : wf state) (injective : injOnState f state) :
    pmov (mapState f state) = mapState f (pmov state) :=
  pmovMapInj f state valid injective

def runChecks : IO Bool := do
  IO.println "PASS parmove pmov_MAP_INJ commutes pmov with map_state"
  pure true

end Flapjack.Test.ParmovePmovMapInjParity
