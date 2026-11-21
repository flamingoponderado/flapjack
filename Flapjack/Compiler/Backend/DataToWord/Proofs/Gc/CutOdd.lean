module

public import Flapjack.Misc.Sptree.Wf
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

/-- Exact HOL `cut_env_adjust_sets_ODD` (`data_to_word_gcProofScript.sml:7948-7961`); HOL `ODD n` is `n % 2 = 1`; HOL free
variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_env_adjust_sets_ODD"]
theorem cut_env_adjust_sets_ODD {α β : Type} {n : Nat} {names : Spt β} {w : α} {s : Spt α} :
    n % 2 = 1 →
      wordSemCutEnv (adjustSets names) (sptInsert n w s) = wordSemCutEnv (adjustSets names) s :=
  fun odd => cutEnv_adjustSets_insertOdd names s n w odd

/-- Exact HOL `cut_envs_adjust_sets_ODD` (`data_to_word_gcProofScript.sml:7963-7974`); HOL `ODD n` is `n % 2 = 1`; HOL free
variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_envs_adjust_sets_ODD"]
theorem cut_envs_adjust_sets_ODD {α β : Type} {n : Nat} {names : Spt β} {w : α} {s : Spt α} :
    n % 2 = 1 →
      wordSemCutEnvs (adjustSets names) (sptInsert n w s) = wordSemCutEnvs (adjustSets names) s :=
  fun odd => cutEnvs_adjustSets_insertOdd names s n w odd

/-- Exact HOL `cut_envs_adjust_sets_insert_ODD` (`data_to_word_gcProofScript.sml:8154-8176`); HOL `ODD n` is `n % 2 = 1`; HOL free
variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_envs_adjust_sets_insert_ODD"
  ]
theorem cut_envs_adjust_sets_insert_ODD {α β : Type} {n : Nat} {names : Spt β} {w : α}
    {t : Spt α} :
    n % 2 = 1 →
      wordSemCutEnvs (adjustSets names) (sptInsert n w t) = wordSemCutEnvs (adjustSets names) t :=
  fun odd => cutEnvs_adjustSets_insertOdd names t n w odd

/-- Exact HOL `cut_names_imp_wf` (`data_to_word_gcProofScript.sml:8235-8239`); HOL free
variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_names_imp_wf"]
theorem cut_names_imp_wf {α β : Type} {s : Spt β} {t x : Spt α} :
    wordSemCutNames s t = some x → sptWf x = true := by
  intro h
  simp only [wordSemCutNames] at h
  split at h
  · cases h; exact sptWfInter t s
  · cases h

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
