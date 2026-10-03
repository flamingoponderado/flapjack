import Flapjack.HolRef

namespace Flapjack.Compiler.Backend.FlatPattern

/-- The original numeric heuristic field; historical HOL function-type comments
are not part of the actual carrier. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "config"]
structure Config where
  patHeuristic : Nat
  deriving DecidableEq, Repr

/-- Retains every natural-number heuristic identifier. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "init_config_def"]
def initConfig (ph : Nat) : Config := ⟨ph⟩

end Flapjack.Compiler.Backend.FlatPattern
