module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackSizeTail
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.InterUnion
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

/-! Restoring related data and word environments from the stack. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps

namespace popEnvMap
/-- Canonical target-state roundtrip for the pop-environment theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end popEnvMap

/-- The word-semantics option addition is ordinary `OPTION_MAP2 (+)`. -/
private theorem optionMapAdd (a b : Option Nat) :
    Option.map₂ (· + ·) a b = wordSemOptionAdd a b := by
  cases a <;> cases b <;> rfl

/-- A restored local root occurs in the saved GC frame. This factors the
membership reasoning in the HOL pop-environment proof. -/
private theorem restored_join_mem {α β : Type} [Nonempty α]
    (env : Spt α) (nonGc gc : List (Nat × β)) (pair : α × β)
    (zero : ∀ p ∈ nonGc, p.1 = 0)
    (member : pair ∈ joinEnv env (sptToAList
      (sptInter (sptUnion (sptFromAList gc) (sptFromAList nonGc)) (adjustSet env)))) :
    pair ∈ joinEnv env gc := by
  rw [interUnionLemma nonGc (sptFromAList gc) env zero] at member
  simp only [joinEnv, List.mem_map, List.mem_filter] at member ⊢
  obtain ⟨⟨key, word⟩, ⟨inList, valid⟩, equal⟩ := member
  have found := (sptMemToAList _ key word).mp inList
  rw [sptLookup_sptInterCases] at found
  cases hgc : sptLookup key (sptFromAList gc) with
  | none => simp [hgc] at found
  | some v =>
    cases hadj : sptLookup key (adjustSet env) with
    | none => simp [hgc, hadj] at found
    | some flag =>
      have veq : v = word := by simpa [hgc, hadj] using found
      subst v
      rw [sptLookup_sptFromAList] at hgc
      exact ⟨(key, word), ⟨sptAListLookup_mem key gc word hgc, valid⟩, equal⟩

/-- A successful source pop has a matching target pop preserving the full relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_pop_env_IMP"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_popEnv {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source source' : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F)
    (values : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat))
    (premises : stateRel conf l1 l2 source target values locs ∧ DataSem.popEnv source = some source') :
    ∃ target' l3 l4 rest, WordSemStateFiniteExact.popEnv target = some target' ∧
      locs = (l3, l4) :: rest ∧ stateRel conf l3 l4 source' target' values rest := by
  obtain ⟨related, pop⟩ := premises
  cases srcStack : source.stack with
  | nil => simp [DataSem.popEnv, srcStack] at pop
  | cons frame frames =>
    have hstack := related.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [srcStack] at hstack
    cases htarget : target.stack with
    | nil => simp [htarget] at hstack
    | cons tframe tframes =>
      rw [htarget] at hstack
      cases hstack with
      | cons head tail =>
        have hlocs := related.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        rw [htarget] at hlocs
        cases locs with
        | nil => cases hlocs
        | cons location rest =>
          cases hlocs with
          | cons locHead locTail =>
            obtain ⟨l3, l4⟩ := location
            cases frame with
            | env size env =>
              cases tframe with
              | stackFrame tsize nonGc gc handler =>
                cases handler with
                | none =>
                  change stackEnvRel size tsize env nonGc gc at head
                  simp [DataSem.popEnv, srcStack] at pop
                  subst source'
                  refine ⟨{target with locals := sptUnion (sptFromAList gc) (sptFromAList nonGc), stack := tframes, localsSize := tsize}, l3, l4, rest, ?_, rfl, ?_⟩
                  · simp [WordSemStateFiniteExact.popEnv, htarget]
                  ·
                      rcases head with ⟨gcKeys, sizeEq, nonGcKeys, gcDistinct, lookupRel⟩
                      rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
                        htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
                      refine ⟨hffi, hclock, ?_, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
                        ?_, ?_, tail, locTail, ?_, hmax, hsizes, ?_, hlim, ?_⟩
                      · exact hhandler
                      · intro _
                        have gcZero : sptAListLookup 0 gc = none := by
                          cases found : sptAListLookup 0 gc with
                          | none => rfl
                          | some value =>
                            have member := sptAListLookup_mem 0 gc value found
                            have bad := (gcKeys (0, value) member).1
                            exact (bad rfl).elim
                        change sptAListLookup 0 nonGc = some (.loc l3 l4) at locHead
                        simp [sptLookup_sptUnion, sptLookup_sptFromAList, gcZero, locHead]
                      · intro key present
                        have gcPresent := (lookupRel key).mp present
                        obtain ⟨v, found⟩ := Option.isSome_iff_exists.mp gcPresent
                        simp [sptLookup_sptUnion, found]
                      · change optionLe (Option.map₂ (· + ·) (wordSemStackSize tframes) tsize) target.stackMax
                        rw [optionMapAdd]
                        rw [optionMapAdd, htarget] at hacc
                        exact optionLe_tail tsize nonGc gc none tframes target.localsSize target.stackMax hacc
                      · exact sizeEq.symm
                      · change memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                          target.store target.memory target.mdomain
                          (values.getD [] ++ joinEnv env (sptToAList
                            (sptInter (sptUnion (sptFromAList gc) (sptFromAList nonGc)) (adjustSet env))) ++
                            [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack frames tframes)
                        simp only [srcStack, htarget, flatStack] at hmem
                        apply memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
                          target.store target.memory target.mdomain _ _ ?_ hmem
                        intro pair member
                        have joined : pair ∈ joinEnv env (sptToAList
                            (sptInter (sptUnion (sptFromAList gc) (sptFromAList nonGc)) (adjustSet env))) →
                            pair ∈ joinEnv env gc := restored_join_mem env nonGc gc pair nonGcKeys
                        simp only [List.mem_append] at member ⊢
                        tauto
                | some h => simp [stackRel] at head
            | exc size env saved =>
              cases tframe with
              | stackFrame tsize nonGc gc handler =>
                cases handler with
                | none => simp [stackRel] at head
                | some h =>
                  obtain ⟨saved', p, q⟩ := h
                  change stackEnvRel size tsize env nonGc gc ∧ saved' = saved at head
                  obtain ⟨head, rfl⟩ := head
                  simp [DataSem.popEnv, srcStack] at pop
                  subst source'
                  refine ⟨{target with locals := sptUnion (sptFromAList gc) (sptFromAList nonGc), stack := tframes, localsSize := tsize, handler := saved'}, l3, l4, rest, ?_, rfl, ?_⟩
                  · simp [WordSemStateFiniteExact.popEnv, htarget]
                  ·
                      rcases head with ⟨gcKeys, sizeEq, nonGcKeys, gcDistinct, lookupRel⟩
                      rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
                        htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
                      refine ⟨hffi, hclock, ?_, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
                        ?_, ?_, tail, locTail, ?_, hmax, hsizes, ?_, hlim, ?_⟩
                      · rfl
                      · intro _
                        have gcZero : sptAListLookup 0 gc = none := by
                          cases found : sptAListLookup 0 gc with
                          | none => rfl
                          | some value =>
                            have member := sptAListLookup_mem 0 gc value found
                            have bad := (gcKeys (0, value) member).1
                            exact (bad rfl).elim
                        change sptAListLookup 0 nonGc = some (.loc l3 l4) at locHead
                        simp [sptLookup_sptUnion, sptLookup_sptFromAList, gcZero, locHead]
                      · intro key present
                        have gcPresent := (lookupRel key).mp present
                        obtain ⟨v, found⟩ := Option.isSome_iff_exists.mp gcPresent
                        simp [sptLookup_sptUnion, found]
                      · change optionLe (Option.map₂ (· + ·) (wordSemStackSize tframes) tsize) target.stackMax
                        rw [optionMapAdd]
                        rw [optionMapAdd, htarget] at hacc
                        exact optionLe_tail tsize nonGc gc (some (saved', p, q)) tframes target.localsSize target.stackMax hacc
                      · exact sizeEq.symm
                      · change memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                          target.store target.memory target.mdomain
                          (values.getD [] ++ joinEnv env (sptToAList
                            (sptInter (sptUnion (sptFromAList gc) (sptFromAList nonGc)) (adjustSet env))) ++
                            [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack frames tframes)
                        simp only [srcStack, htarget, flatStack] at hmem
                        apply memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
                          target.store target.memory target.mdomain _ _ ?_ hmem
                        intro pair member
                        have joined : pair ∈ joinEnv env (sptToAList
                            (sptInter (sptUnion (sptFromAList gc) (sptFromAList nonGc)) (adjustSet env))) →
                            pair ∈ joinEnv env gc := restored_join_mem env nonGc gc pair nonGcKeys
                        simp only [List.mem_append] at member ⊢
                        tauto

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
