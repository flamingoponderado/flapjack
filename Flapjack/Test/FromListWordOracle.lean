-- Generated from the pinned original HOL compiler; do not edit.
module

public import Flapjack.Pancake.WordLang
public import Flapjack.Test.CakeWordOracleHelpers

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Flapjack.Test.FromListWordOracle

open Flapjack.Test.CakeWordOracleHelpers

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | [entry0] =>
      shared_matches0_2 entry0
  | _ => false

end Flapjack.Test.FromListWordOracle
