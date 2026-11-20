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

/-- Intersecting a union distributes over its two left-biased operands. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "inter_union_distrib"]
theorem inter_union_distrib {α β : Type} (x y : Spt α) (z : Spt β) :
    sptInter (sptUnion x y) z = sptUnion (sptInter x z) (sptInter y z) := by
  apply (sptEqThm _ _ ⟨sptWfInter _ _, sptWfUnion _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩⟩).2
  intro key
  simp only [sptLookup_sptInterCases, sptLookup_sptUnion]
  cases sptLookup key x <;> cases sptLookup key y <;> cases sptLookup key z <;> rfl

/-- The reserved-location cut is disjoint from adjusted source variables. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_envs_inter"]
theorem cutEnvs_inter {α β : Type} (names : NumSet) (target first second : Spt β)
    (source cut : Spt α)
    (premises : wordSemCutEnvs (adjustSets names) target = some (first, second) ∧
      DataSem.cutEnv names source = some cut) :
    sptInter (sptFromAList (sptToAList first)) (adjustSet cut) = .ln := by
  have run := premises.1
  by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive (adjustSets names).1 target <;>
    by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive (adjustSets names).2 target <;>
    simp [wordSemCutEnvs, wordSemCutNames, h1, h2] at run
  obtain ⟨firstEq, _⟩ := run
  apply (sptEqThm _ _ ⟨sptWfInter _ _, by simp [sptWf]⟩).2
  intro key
  rw [sptLookup_sptInterCases, sptLookup_sptFromAList_sptToAList, ← firstEq,
    sptLookup_sptInterCases]
  by_cases zero : key = 0
  · subst key
    have absent : sptLookup 0 (adjustSet cut) = none := by
      cases found : sptLookup 0 (adjustSet cut) with
      | none => rfl
      | some value => exact (not_zero_adjustSet cut ((sptMem_iff_lookup _ _).mpr ⟨value, found⟩)).elim
    simp [absent, sptLookup]
  · simp [adjustSets, sptLookup, zero]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
