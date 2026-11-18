module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

/-! Word-environment cut decomposition used by GC allocation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A successful combined cut exposes its two component cuts and their union. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_env_IMP_cut_envs"]
theorem cutEnv_imp_cutEnvs {α : Type} (names : WordLangCutsetsHOL) (locals result : Spt α)
    (run : wordSemCutEnv names locals = some result) :
    ∃ first second, wordSemCutEnvs names locals = some (first, second) ∧
      result = sptUnion second first := by
  cases pairRun : wordSemCutEnvs names locals with
  | none => simp [wordSemCutEnv, pairRun] at run
  | some pair =>
    obtain ⟨first, second⟩ := pair
    simp only [wordSemCutEnv, pairRun] at run
    exact ⟨first, second, rfl, (Option.some.inj run).symm⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
