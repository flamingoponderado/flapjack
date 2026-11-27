module

public import Flapjack.Compiler.Backend.Backend

@[expose] public section

/-! Backend program-record helpers from `backendScript.sml`. -/
namespace Flapjack.Compiler.Backend.Backend
open Flapjack

/-- Original `keep_progs_def`: keep the program list only when the flag is set. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "keep_progs_def"]
def keepProgs {α : Type} (k : Bool) (ps : List α) : List α := if k then ps else []

/-- Original `set_oracle_def`: replace the word-to-word colour oracle. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "set_oracle_def"]
def setOracle (c : Config) (oracle : List (Option (Spt Nat))) : Config :=
  { c with wordToWordConf := { c.wordToWordConf with colOracle := oracle } }

end Flapjack.Compiler.Backend.Backend
