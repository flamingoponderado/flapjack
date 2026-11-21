module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutOdd
public import Flapjack.Misc.Sptree.UnionAlgebra
@[expose] public section

/-! The reserved-register cut facts used by variable allocation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Keep the reserved register when cutting with it added to the live set. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_names_insert_1_insert_1"]
theorem cutNamesInsertOne {α β : Type} (names : Spt α) (env : Spt β) (w : β) :
    wordSemCutNames (sptInsert 1 () (adjustSet names)) (sptInsert 1 w env) =
      (wordSemCutNames (adjustSet names) env).map (sptInsert 1 w) := by
  have absent : ¬ sptMem 1 (adjustSet names) := not_one_adjustSet names
  have guard : LoopSemStateFiniteExact.sptSubsetLive (sptInsert 1 () (adjustSet names)) (sptInsert 1 w env) ↔
      LoopSemStateFiniteExact.sptSubsetLive (adjustSet names) env := by
    constructor
    · intro h key member
      have inBoth := h key ((sptMem_sptInsert key 1 () (adjustSet names)).mpr (Or.inr member))
      rcases (sptMem_sptInsert key 1 w env).mp inBoth with same | old
      · subst key; exact (absent member).elim
      · exact old
    · intro h key member
      rcases (sptMem_sptInsert key 1 () (adjustSet names)).mp member with same | old
      · subst key; exact (sptMem_sptInsert 1 1 w env).mpr (Or.inl rfl)
      · exact (sptMem_sptInsert key 1 w env).mpr (Or.inr (h key old))
  have inter : sptInter (sptInsert 1 w env) (sptInsert 1 () (adjustSet names)) =
      sptInsert 1 w (sptInter env (adjustSet names)) := by
    apply (sptEqThm _ _ ⟨sptWfInter _ _, sptWfInsert _ _ _ (sptWfInter _ _)⟩).2
    intro key
    rw [sptLookup_sptInterCases]
    by_cases same : key = 1
    · subst key; simp [sptLookup_sptInsert_same]
    · rw [sptLookup_sptInsert_ne 1 key w env same,
        sptLookup_sptInsert_ne 1 key () (adjustSet names) same,
        sptLookup_sptInsert_ne 1 key w (sptInter env (adjustSet names)) same,
        sptLookup_sptInterCases]
  unfold wordSemCutNames
  by_cases live : LoopSemStateFiniteExact.sptSubsetLive (adjustSet names) env
  · simp [live, guard.mpr live, inter]
  · have notLive : ¬ LoopSemStateFiniteExact.sptSubsetLive (sptInsert 1 () (adjustSet names)) (sptInsert 1 w env) :=
      fun h => live (guard.mp h)
    simp [live, notLive]

/-- The paired cut also retains the inserted reserved register. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_env_insert_1"]
theorem cutEnvInsertOne {α β : Type} (names : Spt α) (env : Spt β) (w : β) :
    wordSemCutEnv ((adjustSets names).1, sptInsert 1 () (adjustSets names).2) (sptInsert 1 w env) =
      (wordSemCutEnv (adjustSets names) env).map (sptInsert 1 w) := by
  have absent : ¬ sptMem 1 (.ls () : NumSet) := by
    intro member
    obtain ⟨v, found⟩ := (sptMem_iff_lookup 1 (.ls ())).mp member
    simp [sptLookup] at found
  have zeroCut : wordSemCutNames (.ls () : NumSet) (sptInsert 1 w env) = wordSemCutNames (.ls ()) env :=
    cutNames_insert_notMem (.ls ()) env 1 w absent
  have secondCut := cutNamesInsertOne names env w
  simp only [wordSemCutEnv, wordSemCutEnvs, adjustSets, zeroCut, secondCut]
  cases first : wordSemCutNames (.ls () : NumSet) env <;>
    cases second : wordSemCutNames (adjustSet names) env <;> simp
  rename_i a b
  rw [sptInsert_union 1 w b, ← sptUnion_assoc, ← sptInsert_union]
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
