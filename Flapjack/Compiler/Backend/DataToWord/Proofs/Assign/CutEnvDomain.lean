module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutEnvProperties

@[expose] public section

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- A retained source variable is retained by the adjusted word cut. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "IN_adjust_var_lemma"]
theorem in_adjustVar_lemma {α β : Type} (names : NumSet) (source cut : Spt α)
    (target first second : Spt β) (n : Nat)
    (premises : DataSem.cutEnv names source = some cut ∧
      wordSemCutEnvs (adjustSets names) target = some (first, second) ∧
      sptDomain cut n) : sptDomain second (adjustVar n) := by
  have sourceLookup : (sptLookup n cut).isSome := by
    obtain ⟨value, found⟩ := (sptMem_iff_lookup n cut).mp premises.2.2
    simp [found]
  have namesLookup := (cutEnv_imp_mem names source cut n premises.1).mp sourceLookup
  have targetLookup := (adjustVar_cutEnvs_imp_mem names target (first, second) n premises.2.1).2.mpr namesLookup
  cases found : sptLookup (adjustVar n) second with
  | none => simp [found] at targetLookup
  | some value => exact (sptMem_iff_lookup _ _).mpr ⟨value, found⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
