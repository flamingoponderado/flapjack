module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.CutEnvsOdd
@[expose] public section

/-! Joined adjusted cuts are unaffected by odd temporary insertions. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- An odd temporary does not change a cut using adjusted source names. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_env_adjust_sets_insert_ODD"]
theorem cutEnv_adjustSets_insertOdd {α β : Type} (names : Spt α) (env : Spt β)
    (n : Nat) (value : β) (odd : n % 2 = 1) :
    wordSemCutEnv (adjustSets names) (sptInsert n value env) =
      wordSemCutEnv (adjustSets names) env := by
  simp only [wordSemCutEnv, cutEnvs_adjustSets_insertOdd names env n value odd]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
