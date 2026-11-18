module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PopEnv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Move

@[expose] public section

/-! Restoring a returned value after popping a related environment. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace popEnvSetVarMap
/-- Canonical target-state roundtrip for the pop-and-update theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end popEnvSetVarMap

/-- The location recorded in a related stack frame is restored by its pop.
This is the location part of the HOL pop-and-update argument. -/
private theorem popped_zero {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 l3 l4 : Nat)
    (source : DataSem.State C F) (target target' : WordSemStateFiniteExact width C F)
    (values : Option (List (DataSem.Value × WordLocW width))) (rest : List (Nat × Nat))
    (related : stateRel conf l1 l2 source target values ((l3,l4) :: rest))
    (pop : WordSemStateFiniteExact.popEnv target = some target') :
    sptLookup 0 target'.locals = some (.loc l3 l4) := by
  have hstack := related.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlocs := related.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases ht : target.stack with
  | nil => simp [WordSemStateFiniteExact.popEnv, ht] at pop
  | cons tf ts =>
    rw [ht] at hstack hlocs
    cases hlocs with
    | cons locHead locTail =>
      cases hs : source.stack with
      | nil => simp [hs] at hstack
      | cons sf ss =>
        rw [hs] at hstack
        cases hstack with
        | cons frameRel tail =>
          cases tf with
          | stackFrame size nonGc gc handler =>
            have gcKeys : ∀ p ∈ gc, p.1 ≠ 0 := by
              cases sf <;> cases handler <;> simp_all [stackRel, stackEnvRel]
              all_goals intro a b member
              all_goals first | exact (frameRel.1 a b member).1 | exact (frameRel.1.1 a b member).1
            have gcZero : sptAListLookup 0 gc = none := by
              cases found : sptAListLookup 0 gc with
              | none => rfl
              | some value =>
                have member := sptAListLookup_mem 0 gc value found
                exact (gcKeys (0, value) member rfl).elim
            change sptAListLookup 0 nonGc = some (.loc l3 l4) at locHead
            cases handler <;> simp [WordSemStateFiniteExact.popEnv, ht] at pop
            all_goals subst target'
            all_goals simp [sptLookup_sptUnion, sptLookup_sptFromAList, gcZero, locHead]

/-- Popping a source environment and storing its returned value has a
corresponding target pop and store preserving the complete state relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_pop_env_set_var_IMP"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_popEnv_setVar {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source source' : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (value : Flapjack.Compiler.Backend.DataSem.Value) (word : WordLocW width) (dest : Nat)
    (premises : stateRel conf l1 l2 source target (some [(value, word)]) locs ∧
      DataSem.popEnv source = some source') :
    ∃ target' l3 l4 rest, WordSemStateFiniteExact.popEnv target = some target' ∧
      locs = (l3, l4) :: rest ∧
      stateRel conf l3 l4 (DataSem.setVar dest value source')
        (WordSemStateFiniteExact.setVar (adjustVar dest) word target') none rest := by
  obtain ⟨target', l3, l4, rest, pop, locations, related⟩ :=
    stateRel_popEnv conf l1 l2 source source' target (some [(value, word)]) locs premises
  have zero := popped_zero conf l1 l2 l3 l4 source target target' (some [(value, word)]) rest
    (by simpa [locations] using premises.1) pop
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
  have root : memoryRel conf target'.be (holThe source'.tstamps) source'.refs source'.space
      target'.store target'.memory target'.mdomain
      ((value, word) :: joinEnv source'.locals
        (sptToAList (sptInter target'.locals (adjustSet source'.locals))) ++
        [(theGlobal source'.global, holFapply target'.store .globals)] ++ flatStack source'.stack target'.stack) := by
    simpa using hmem
  have relatedNone : stateRel conf l3 l4 source' target' none rest := by
    refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
      (fun _ => zero), hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, ?_⟩
    exact memoryRel_tl conf target'.be (holThe source'.tstamps) source'.refs source'.space
      target'.store target'.memory target'.mdomain (value, word) _ root
  exact ⟨target', l3, l4, rest, pop, locations,
    stateRel_insertRoot conf l3 l4 source' target' rest dest value word relatedNone root⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
