module

public import Flapjack.Compiler.Backend.Backend

@[expose] public section

/-! backendScript.sml: `set_oracle_def`, the register-allocation oracle
installer used by the backend correctness statements. -/
namespace Flapjack.Compiler.Backend.Backend

/-- Exact HOL `backend$set_oracle_def`: replace only the word-to-word colouring
oracle, keeping every other configuration field. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "set_oracle_def"]
def setOracle (c : Config) (oracle : List (Option (Flapjack.Spt Nat))) : Config :=
  { c with wordToWordConf := { c.wordToWordConf with colOracle := oracle } }

end Flapjack.Compiler.Backend.Backend
