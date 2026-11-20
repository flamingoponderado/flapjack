module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AdjustedSet
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env
public import Flapjack.Misc.Sptree.Wf

@[expose] public section

/-! Odd temporary variables do not affect adjusted data-variable cutsets. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A cut is unaffected by insertion outside its name set. This is the
general sparse-tree observation used by the source's odd-variable argument. -/
private theorem cutNames_insert_notMem {α β : Type} (names : Spt α) (env : Spt β)
    (key : Nat) (value : β) (absent : ¬ sptMem key names) :
    wordSemCutNames names (sptInsert key value env) = wordSemCutNames names env := by
  have guard : LoopSemStateFiniteExact.sptSubsetLive names (sptInsert key value env) ↔
      LoopSemStateFiniteExact.sptSubsetLive names env := by
    constructor
    · intro h other member
      have present := h other member
      rw [sptMem_sptInsert] at present
      rcases present with same | present
      · subst other; exact (absent member).elim
      · exact present
    · intro h other member
      exact (sptMem_sptInsert other key value env).mpr (Or.inr (h other member))
  have inter : sptInter (sptInsert key value env) names = sptInter env names := by
    apply (sptEqThm _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩).2
    intro other
    rw [sptLookup_sptInterCases, sptLookup_sptInterCases]
    by_cases same : other = key
    · subst other
      have noLookup : sptLookup key names = none := by
        cases found : sptLookup key names with
        | none => rfl
        | some v => exact (absent ((sptMem_iff_lookup key names).mpr ⟨v, found⟩)).elim
      simp [noLookup]
    · rw [sptLookup_sptInsert_ne key other value env same]
  unfold wordSemCutNames
  by_cases live : LoopSemStateFiniteExact.sptSubsetLive names env
  · simp [live, guard.mpr live, inter]
  · have notLive : ¬ LoopSemStateFiniteExact.sptSubsetLive names (sptInsert key value env) :=
      fun h => live (guard.mp h)
    simp [live, notLive]

/-- An odd temporary does not change a cut using adjusted source names. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_names_adjust_set_insert_ODD"]
theorem cutNames_adjustSet_insertOdd {α β : Type} (names : Spt α) (env : Spt β)
    (n : Nat) (value : β) (odd : n % 2 = 1) :
    wordSemCutNames (adjustSet names) (sptInsert n value env) =
      wordSemCutNames (adjustSet names) env := by
  apply cutNames_insert_notMem
  intro member
  obtain ⟨k, eq, _⟩ := (adjustSet_domain names n).mp member
  simp [adjustVar] at eq
  omega

/-- Both component cuts are unchanged by an odd temporary. This supports the
allocation theorem, which observes the pair before the cuts are joined. -/
theorem cutEnvs_adjustSets_insertOdd {α β : Type} (names : Spt α) (env : Spt β)
    (n : Nat) (value : β) (odd : n % 2 = 1) :
    wordSemCutEnvs (adjustSets names) (sptInsert n value env) =
      wordSemCutEnvs (adjustSets names) env := by
  have notZero : ¬ sptMem n (.ls () : NumSet) := by
    intro member
    obtain ⟨v, found⟩ := (sptMem_iff_lookup n (.ls ())).mp member
    cases n <;> simp_all
  simp only [wordSemCutEnvs, adjustSets]
  rw [cutNames_insert_notMem (.ls ()) env n value notZero,
    cutNames_adjustSet_insertOdd names env n value odd]

/-- An odd temporary does not change a cut using adjusted source names. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_env_adjust_sets_insert_ODD"]
theorem cutEnv_adjustSets_insertOdd {α β : Type} (names : Spt α) (env : Spt β)
    (n : Nat) (value : β) (odd : n % 2 = 1) :
    wordSemCutEnv (adjustSets names) (sptInsert n value env) =
      wordSemCutEnv (adjustSets names) env := by
  simp only [wordSemCutEnv, cutEnvs_adjustSets_insertOdd names env n value odd]

/-- Inserting key one does not change the adjusted cut. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_names_adjust_set_insert_1"]
theorem cutNames_adjustSet_insert_one {α β : Type} (names : Spt α) (env : Spt β) (w : β) :
    wordSemCutNames (adjustSet names) (sptInsert 1 w env) = wordSemCutNames (adjustSet names) env :=
  cutNames_insert_notMem (adjustSet names) env 1 w (not_one_adjustSet names)

/-- Inserting key three does not change the adjusted cut. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_names_adjust_set_insert_3"]
theorem cutNames_adjustSet_insert_three {α β : Type} (names : Spt α) (env : Spt β) (w : β) :
    wordSemCutNames (adjustSet names) (sptInsert 3 w env) = wordSemCutNames (adjustSet names) env :=
  cutNames_insert_notMem (adjustSet names) env 3 w (not_three_adjustSet names)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
