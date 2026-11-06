import Flapjack.Misc.Sptree

/-! Variable and live-set layout for the data-to-word pass. -/
namespace Flapjack.Compiler.Backend.DataToWord

/-- Data variables occupy even word-language variable slots starting at two. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "adjust_var_def"]
def adjustVar (n : Nat) : Nat := 2 * n + 2

/-- Convert a data-language name map to the corresponding word live set. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "adjust_set_def"]
def adjustSet {α : Type} (names : Spt α) : NumSet :=
  sptFromAList ((sptToAList names).map fun (n, _) => (adjustVar n, ()))

/-- Pair the fixed initial live set with the adjusted source live set. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "adjust_sets_def"]
def adjustSets {α : Type} (names : Spt α) : NumSet × NumSet :=
  (.ls (), adjustSet names)

end Flapjack.Compiler.Backend.DataToWord
