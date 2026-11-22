module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.CutState

@[expose] public section

/-! The argument-free specialization of `state_rel_cut_state_opt_SOME`
(`data_to_wordProofScript.sml` lines 123-126). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

namespace reviewedStateRelCutEnvImpCutEnvMap
/-- Canonical roundtrip for the target state used by this HOL port. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end reviewedStateRelCutEnvImpCutEnvMap

/-- A successful source environment cut has a matching target cut, and the
cut source state is related both to the uncut and to the cut target state.
HOL derives this by specializing `state_rel_cut_state_opt_SOME` at `args = []`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "state_rel_cut_env_IMP_cut_env"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_cutEnv_imp_cutEnv {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (s : Flapjack.Compiler.Backend.DataSem.State C F)
    (locs : List (Nat × Nat)) (l2 l1 : Nat) (keptNames : NumSet)
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (env : Spt Flapjack.Compiler.Backend.DataSem.Value)
    (premises : stateRel c l1 l2 s t none locs ∧ DataSem.cutEnv keptNames s.locals = some env) :
    ∃ y, wordSemCutEnv (adjustSets keptNames) t.locals = some y ∧
      stateRel c l1 l2 { s with locals := env } t none locs ∧
      stateRel c l1 l2 { s with locals := env } { t with locals := y } none locs := by
  obtain ⟨related, cutRun⟩ := premises
  obtain ⟨y, _, cut, _, _, _, rel1, rel2⟩ :=
    Assign.stateRel_cutStateOpt_some c l1 l2 s t locs [] [] keptNames { s with locals := env }
      ⟨related, rfl, by simp [DataSem.cutStateOpt, DataSem.cutState, cutRun]⟩
  exact ⟨y, cut, rel1, rel2⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs
