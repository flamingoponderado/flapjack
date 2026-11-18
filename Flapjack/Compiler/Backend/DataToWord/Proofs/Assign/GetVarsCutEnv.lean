module

public import Flapjack.Compiler.Backend.DataLive.Proofs.State

@[expose] public section

/-! Reading variables after retaining them in an environment cut. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend

/-- Cutting an environment preserves a successful read of retained variables. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "get_vars_cut_env"]
theorem getVars_cutEnv {α : Type} (names : NumSet) (source target : Spt α)
    (vars : List Nat) (values : List α)
    (premises : DataSem.cutEnv names source = some target ∧
      DataSem.getVars vars source = some values ∧ (∀ v ∈ vars, sptMem v names)) :
    DataSem.getVars vars target = some values := by
  obtain ⟨cutRun, read, kept⟩ := premises
  induction vars generalizing values with
  | nil => simpa [DataSem.getVars] using read
  | cons name vars ih =>
    cases first : DataSem.getVar name source with
    | none => simp [DataSem.getVars, first] at read
    | some value =>
      cases rest : DataSem.getVars vars source with
      | none => simp [DataSem.getVars, first, rest] at read
      | some tail =>
        have present : sptMem name names := kept name (by simp)
        have cutFirst : DataSem.getVar name target = some value := by
          change sptLookup name source = some value at first
          simpa [DataSem.getVar, present, first] using DataLive.cutEnv_lookup names source target cutRun name
        have cutRest := ih tail rest (fun key member => kept key (by simp [member]))
        simp [DataSem.getVars, first, rest] at read
        subst values
        simp [DataSem.getVars, cutFirst, cutRest]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
