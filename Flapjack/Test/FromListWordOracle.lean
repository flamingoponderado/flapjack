-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang
import Flapjack.Test.CakeWordOracleHelpers

namespace Flapjack.Test.FromListWordOracle

open Flapjack.Test.CakeWordOracleHelpers

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0] =>
      shared_matches0_2 entry0
  | _ => false

end Flapjack.Test.FromListWordOracle
