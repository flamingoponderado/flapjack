module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.CutState
public import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
@[expose] public section

/-! Sparse-tree, environment and clock prerequisites for integer comparison. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
set_option maxRecDepth 8192
/-- Well-formed sparse trees are equal when all of their lookups agree. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "IMP_spt_eq"]
theorem impSptEq {α : Type} (t1 t2 : Spt α) :
    sptWf t1 = true ∧ sptWf t2 = true ∧ (∀ n, sptLookup n t1 = sptLookup n t2) → t1 = t2 := by
  rintro ⟨wf1, wf2, lookup⟩
  exact (sptEqThm t1 t2 ⟨wf1, wf2⟩).2 lookup
namespace ComparisonSetupWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end ComparisonSetupWitness

/-- A successful environment cut is reconstructed from its permuted association list. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "env_to_list_cut_env_IMP"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem envToListCutEnvImp {width stateWidth : Nat} [NeZero width] [NeZero stateWidth] {C F : Type}
    (x : Spt (WordLocW width)) (t : WordSemStateFiniteExact stateWidth C F)
    (entries : List (Nat × WordLocW width)) (permute : Nat → Nat → Nat)
    (names : WordLangCutsetsHOL) (env : Spt (WordLocW width)) :
    wordSemEnvToList x t.permute = (entries, permute) ∧ wordSemCutEnv names env = some x →
      sptFromAList entries = x := by
  rintro ⟨run, cut⟩
  have wf : sptWf x = true := by
    cases h : wordSemCutEnvs names env with
    | none => simp [wordSemCutEnv, h] at cut
    | some pair =>
      obtain ⟨first, second⟩ := pair
      simp only [wordSemCutEnv, h, Option.some.injEq] at cut
      subst x
      exact sptWfUnion _ _ ⟨(cutEnvs_wf names env first second h).2, (cutEnvs_wf names env first second h).1⟩
  apply (sptEqThm _ _ ⟨sptWfFromAList _, wf⟩).2
  intro key
  rw [sptLookup_sptFromAList]
  exact (wordSemEnvToListLookupEquiv x t.permute entries permute run).1 key
/-- The target clock limit exceeds one full word range even after one tick. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "dimword_LESS_MustTerminate_limit"
  (word_dimension_as_width := width)]
theorem dimwordLessMustTerminateLimit (width : Nat) [NeZero width] : goodDimindex width → 2 ^ width < wordSemMustTerminateLimit width - 1 := by
  intro good
  have bound : 1 < (2 : Nat) ^ width := by
    rcases good with h | h <;> subst width <;> norm_num
  simp only [wordSemMustTerminateLimit]
  omega
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
