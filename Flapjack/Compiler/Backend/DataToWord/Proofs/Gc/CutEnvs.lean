module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

/-! Word-environment cut decomposition used by GC allocation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

namespace singletonStateMap
/-- Canonical target-state roundtrip for the singleton update theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end singletonStateMap

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

/-- Updating a singleton list is the same as updating its one variable. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "set_vars_sing"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setVars_singleton {width : Nat} [NeZero width] {C F : Type}
    (name : Nat) (value : WordLocW width) (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.setVars [name] [value] state =
      WordSemStateFiniteExact.setVar name value state := by
  rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
