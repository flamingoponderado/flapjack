module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutOdd
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.CutState
public import Flapjack.Compiler.Backend.DataLive.Proofs.State

@[expose] public section

/-! Properties of the source and word environment cuts used by calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

namespace cutEnvPropertiesMap
/-- Canonical target-state roundtrip for the reserved-location theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end cutEnvPropertiesMap

/-- A successful data cut has exactly the domain of its requested names. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_env_IMP_MEM"]
theorem cutEnv_imp_mem {α : Type} (names : NumSet) (env cut : Spt α) (key : Nat)
    (run : DataSem.cutEnv names env = some cut) :
    (sptLookup key cut).isSome ↔ (sptLookup key names).isSome := by
  have lookup := DataLive.cutEnv_lookup names env cut run key
  unfold DataSem.cutEnv at run
  split at run
  · rename_i subset
    cases hn : sptLookup key names with
    | none => simp [lookup, sptMem, sptDomain, hn]
    | some name =>
      have present := subset key ((sptMem_iff_lookup key names).mpr ⟨name, hn⟩)
      obtain ⟨v, hv⟩ := (sptMem_iff_lookup key env).mp present
      simp [lookup, sptMem, sptDomain, hn, hv]
  · simp at run

/-- A successful word cut retains only bindings from the original tree. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_env_IMP_lookup"]
theorem wordCutEnv_imp_lookup {α : Type} (names : WordLangCutsetsHOL) (env cut : Spt α)
    (key : Nat) (value : α)
    (premises : wordSemCutEnv names env = some cut ∧ sptLookup key cut = some value) :
    sptLookup key env = some value :=
  Assign.cutEnv_lookup names env cut key value premises

/-- A successful data cut preserves lookups at requested names. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_env_IMP_lookup_EQ"]
theorem cutEnv_imp_lookup_eq {α : Type} (names : NumSet) (env cut : Spt α) (key : Nat)
    (premises : DataSem.cutEnv names env = some cut ∧ sptDomain names key) :
    sptLookup key cut = sptLookup key env := by
  rw [DataLive.cutEnv_lookup names env cut premises.1 key]
  simp [sptMem, premises.2]

/-- Adjusted source variables never occupy the reserved key zero. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "NOT_0_domain"]
theorem not_zero_adjustSet {α : Type} (names : Spt α) : ¬ sptDomain (adjustSet names) 0 := by
  intro member
  obtain ⟨key, equal, _⟩ := (adjustSet_domain names 0).mp member
  simp [adjustVar] at equal

/-- Both word cuts are intersections of the source environment and names.
This internal fact packages the success cases used in the HOL cut proofs. -/
private theorem cutEnvs_shape {α : Type} (names : WordLangCutsetsHOL) (env : Spt α)
    (cut : Spt α × Spt α) (run : wordSemCutEnvs names env = some cut) :
    cut.1 = sptInter env names.1 ∧ cut.2 = sptInter env names.2 := by
  by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive names.1 env <;>
    by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive names.2 env <;>
    simp [wordSemCutEnvs, wordSemCutNames, h1, h2] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨rfl, rfl⟩

/-- Success of the two cuts entails that the second name set is live. -/
private theorem cutEnvs_second_subset {α : Type} (names : WordLangCutsetsHOL) (env : Spt α)
    (cut : Spt α × Spt α) (run : wordSemCutEnvs names env = some cut) :
    LoopSemStateFiniteExact.sptSubsetLive names.2 env := by
  by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive names.1 env <;>
    by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive names.2 env <;>
    simp_all [wordSemCutEnvs, wordSemCutNames]

/-- Cutting the adjusted pair preserves the reserved location in its first half. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_env_adjust_set_lookup_0"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem cutEnvs_adjust_lookup_zero {width : Nat} [NeZero width] {C F A : Type}
    (names : Spt A) (target : WordSemStateFiniteExact width C F)
    (cut : Spt (WordLocW width) × Spt (WordLocW width))
    (run : wordSemCutEnvs (adjustSets names) target.locals = some cut) :
    sptLookup 0 cut.1 = sptLookup 0 target.locals := by
  have shape := cutEnvs_shape (adjustSets names) target.locals cut run
  rw [shape.1, sptLookup_sptInterCases]
  cases found : sptLookup 0 target.locals <;> simp [adjustSets, sptLookup]

/-- The adjusted second cut cannot contain the reserved key. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_envs_SND_nonzero"]
theorem cutEnvs_adjust_second_zero {α β : Type} (names : Spt α) (env : Spt β)
    (cut : Spt β × Spt β) (run : wordSemCutEnvs (adjustSets names) env = some cut) :
    sptLookup 0 cut.2 = none := by
  have shape := cutEnvs_shape (adjustSets names) env cut run
  have noLookup : sptLookup 0 (adjustSet names) = none := by
    cases found : sptLookup 0 (adjustSet names) with
    | none => rfl
    | some v => exact (not_zero_adjustSet names ((sptMem_iff_lookup _ _).mpr ⟨v, found⟩)).elim
  rw [shape.2, sptLookup_sptInterCases]
  simp [adjustSets, noLookup]

/-- A binding in the second cut was present in the environment and cutset. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_env_res_IS_SOME_IMP"]
theorem cutEnvs_second_isSome {α : Type} (names : WordLangCutsetsHOL) (env : Spt α)
    (cut : Spt α × Spt α) (key : Nat)
    (premises : wordSemCutEnvs names env = some cut ∧ (sptLookup key cut.2).isSome) :
    (sptLookup key env).isSome ∧ (sptLookup key names.2).isSome := by
  have shape := cutEnvs_shape names env cut premises.1
  rw [shape.2, sptLookup_sptInterCases] at premises
  cases h1 : sptLookup key env <;> cases h2 : sptLookup key names.2 <;> simp_all

/-- A lookup retained in the second cut equals the original lookup. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "lookup_adjust_var_after_cut"]
theorem lookup_adjustVar_after_cut {α : Type} (names : WordLangCutsetsHOL) (env : Spt α)
    (cut : Spt α × Spt α) (key : Nat) (v1 v2 : α)
    (premises : sptLookup (adjustVar key) cut.2 = some v1 ∧
      wordSemCutEnvs names env = some cut ∧ sptLookup (adjustVar key) env = some v2) : v1 = v2 := by
  have shape := cutEnvs_shape names env cut premises.2.1
  rw [shape.2, sptLookup_sptInterCases, premises.2.2] at premises
  cases found : sptLookup (adjustVar key) names.2 <;> simp_all

/-- The second adjusted cut contains only even keys and exactly the
adjusted keys present in the source name tree. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "adjust_var_cut_env_IMP_MEM"]
theorem adjustVar_cutEnvs_imp_mem {α β : Type} (names : Spt α) (env : Spt β)
    (cut : Spt β × Spt β) (key : Nat) (run : wordSemCutEnvs (adjustSets names) env = some cut) :
    (∀ wordKey, sptDomain cut.2 wordKey → wordKey % 2 = 0) ∧
      ((sptLookup (adjustVar key) cut.2).isSome ↔ (sptLookup key names).isSome) := by
  have shape := cutEnvs_shape (adjustSets names) env cut run
  have subset := cutEnvs_second_subset (adjustSets names) env cut run
  constructor
  · intro key member
    have named : sptDomain (adjustSet names) key := by
      obtain ⟨v, hv⟩ := (sptMem_iff_lookup key cut.2).mp member
      rw [shape.2, sptLookup_sptInterCases] at hv
      cases hn : sptLookup key (adjustSet names) with
      | none => simp [adjustSets, hn] at hv
      | some val => exact (sptMem_iff_lookup key (adjustSet names)).mpr ⟨val, hn⟩
    obtain ⟨sourceKey, equal, _⟩ := (adjustSet_domain names key).mp named
    rw [equal]
    simp [adjustVar]
  · rw [shape.2, sptLookup_sptInterCases]
    simp only [adjustSets, lookup_adjustSet_map]
    cases hn : sptLookup key names with
    | none => simp
    | some v =>
      have named : sptMem (adjustVar key) (adjustSet names) := by
        apply (sptMem_iff_lookup _ _).mpr
        refine ⟨(), ?_⟩
        simp [lookup_adjustSet_map, hn]
      have envPresent := subset (adjustVar key) named
      obtain ⟨w, hw⟩ := (sptMem_iff_lookup _ _).mp envPresent
      simp [hw]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
