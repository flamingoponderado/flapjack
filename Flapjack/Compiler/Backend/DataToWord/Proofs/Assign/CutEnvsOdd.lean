module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutNamesOdd
@[expose] public section

/-! Adjusted environment cuts used by the assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Both component cuts are unchanged by an odd temporary. This supports the
allocation theorem, which observes the pair before the cuts are joined. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_envs_adjust_sets_insert_ODD"]
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

/-- Every name in an adjusted set comes from an original name. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "IN_domain_adjust_set_IMP"]
theorem inDomainAdjustSetImp {α : Type} (names : Spt α) (key : Nat)
    (present : sptDomain (adjustSet names) key) :
    ∃ original, key = adjustVar original ∧ sptDomain names original :=
  (adjustSet_domain names key).mp present

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
