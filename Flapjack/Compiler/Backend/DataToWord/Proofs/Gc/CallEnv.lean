module

public import Flapjack.Compiler.Backend.DataSpace.Proofs.State
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AdjustedSet
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordMlInvGetVars
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax
public import Flapjack.Compiler.Backend.WordToStack.Proofs.CallLocalRecovery
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateLaws
public import Flapjack.Misc.Sptree.FromList.Domain

@[expose] public section

/-! Variable and environment facts for data-to-word call simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace callEnvMap
/-- Canonical target-state roundtrip for word variable reads. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end callEnvMap

/-- A successful data variable read preserves list length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_vars_IMP_LENGTH"]
theorem getVars_imp_length {α : Type} (names : List Nat) (values : List α) (env : Spt α)
    (read : DataSem.getVars names env = some values) : names.length = values.length :=
  (DataSpace.getVars_length names env values read).symm

/-- A successful word variable read preserves list length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_vars_IMP_LENGTH_word"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordGetVars_imp_length {width : Nat} [NeZero width] {C F : Type}
    (names : List Nat) (values : List (WordLocW width)) (state : WordSemStateFiniteExact width C F)
    (read : WordSemStateFiniteExact.getVars names state = some values) :
    names.length = values.length :=
  (WordSemStateFiniteExact.getVarsLengthLemma names state values read).symm

/-- The adjusted data index skips the reserved word return location. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "lookup_adjust_var_fromList2"]
theorem lookup_adjustVar_fromList2 {α : Type} (n : Nat) (w : α) (ws : List α) :
    sptLookup (DataToWord.adjustVar n) (sptFromList2 (w :: ws)) = sptLookup n (sptFromList ws) := by
  rw [WordToStackProofs.fromList2Lookup, sptLookupFromList_getElem?]
  simp [DataToWord.adjustVar]

/-- The word-semantics option addition is `OPTION_MAP2 (+)`. -/
private theorem optionMapAdd (a b : Option Nat) :
    Option.map₂ (· + ·) a b = wordSemOptionAdd a b := by
  cases a <;> cases b <;> rfl

/-- New argument roots come from the paired call arguments. This helper
factors the membership reasoning in the HOL call-environment proof. -/
theorem callJoin_mem {width : Nat} [NeZero width]
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (words : List (WordLocW width)) (loc : WordLocW width)
    (pair : Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)
    (member : pair ∈ joinEnv (sptFromList values) (sptToAList
      (sptInter (sptFromList2 (loc :: words)) (adjustSet (sptFromList values))))) :
    pair ∈ values.zip words := by
  simp only [joinEnv, List.mem_map, List.mem_filter] at member
  obtain ⟨⟨key, word⟩, ⟨entry, valid⟩, pairEq⟩ := member
  have found := (sptMemToAList _ key word).mp entry
  rw [sptLookup_sptInterCases] at found
  cases hw : sptLookup key (sptFromList2 (loc :: words)) with
  | none => simp [hw] at found
  | some w =>
    cases ha : sptLookup key (adjustSet (sptFromList values)) with
    | none => simp [hw, ha] at found
    | some a =>
      have wordEq : w = word := by simpa [hw, ha] using found
      subst w
      have keyEq : key = adjustVar ((key - 2) / 2) := by
        simp only [adjustVar]
        simp only [decide_eq_true_eq] at valid
        omega
      rw [keyEq, lookup_adjustVar_fromList2, sptLookupFromList_getElem?] at hw
      rw [keyEq, lookup_adjustSet_map, sptLookupFromList_getElem?] at ha
      cases hv : values[(key - 2) / 2]? with
      | none => simp [hv] at ha
      | some v =>
        have pairValue : (v, word) = pair := by
          simpa [sptLookupFromList_getElem?, hv, holThe] using pairEq
        rw [← pairValue]
        apply List.mem_iff_getElem?.mpr
        refine ⟨(key - 2) / 2, ?_⟩
        rw [List.getElem?_zip_eq_some]
        exact ⟨hv, hw⟩

/-- Entering related data and word calls preserves the full state relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_call_env"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_callEnv {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 l5 l6 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (args : List Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value) (words : List (WordLocW width)) (size : Option Nat)
    (premises : DataSem.getVars args source.locals = some values ∧
      WordSemStateFiniteExact.getVars (args.map adjustVar) target = some words ∧
      stateRel conf l5 l6 source target none locs) :
    stateRel conf l1 l2 (DataSem.callEnv values size (DataSem.decClock source))
      (WordSemStateFiniteExact.callEnv (.loc l1 l2 :: words) size
        (WordSemStateFiniteExact.decClock target)) none locs := by
  obtain ⟨sourceRead, targetRead, related⟩ := premises
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
  refine ⟨hffi, ?_, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
    ?_, ?_, hstack, hlocs, ?_, ?_, hsizes, rfl, hlim, ?_⟩
  · simpa [DataSem.callEnv, DataSem.decClock, WordSemStateFiniteExact.callEnv,
      WordSemStateFiniteExact.decClock] using congrArg (fun n : Nat => n - 1) hclock
  · intro _
    simp [WordSemStateFiniteExact.callEnv, WordToStackProofs.fromList2Lookup]
  · intro key present
    change (sptLookup key (sptFromList values)).isSome = true at present
    change (sptLookup (adjustVar key) (sptFromList2 (.loc l1 l2 :: words))).isSome = true
    rw [lookup_adjustVar_fromList2]
    have eqLen : values.length = words.length := by
      have hs := getVars_imp_length args values source.locals sourceRead
      have ht := wordGetVars_imp_length (args.map adjustVar) words target targetRead
      simp only [List.length_map] at ht
      exact hs.symm.trans ht
    rw [sptLookupFromList_getElem?] at present ⊢
    apply Option.isSome_iff_exists.mpr
    have inRange : key < values.length := by simpa using present
    have wordRange : key < words.length := by omega
    exact ⟨words[key], by simp [wordRange]⟩
  · change optionLe (Option.map₂ (· + ·) (wordSemStackSize target.stack) size)
      (wordSemOptionMax target.stackMax (wordSemOptionAdd (wordSemStackSize target.stack) size))
    rw [optionMapAdd, WordSemStateFiniteExact.wordSemOptionMax_eq, optionLe_max_right]
    exact Or.inr (optionLe_refl _)
  · change optionLe (wordSemOptionMax target.stackMax (wordSemOptionAdd (wordSemStackSize target.stack) size))
      (Option.map₂ max source.stackMax (Option.map₂ (· + ·) (DataSem.sizeOfStack source.stack) size))
    have stackEq := stackRel_sizeOfStack hstack
    rw [WordSemStateFiniteExact.wordSemOptionMax_eq, stackEq, ← optionMapAdd, optionLe_max]
    constructor
    · rw [optionLe_max_right]
      exact Or.inl hmax
    · rw [optionLe_max_right]
      exact Or.inr (optionLe_refl _)
  · change memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (joinEnv (sptFromList values) (sptToAList
        (sptInter (sptFromList2 (.loc l1 l2 :: words)) (adjustSet (sptFromList values)))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
    obtain ⟨heap, limit, a, sp, sp1, gens, hstore, hinv, hbound, hspace⟩ := hmem
    refine ⟨heap, limit, a, sp, sp1, gens, hstore, ?_, hbound, hspace⟩
    let rest := [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
    have added := wordMlInv_getVars heap target.be a sp sp1 gens limit (holThe source.tstamps)
      conf source.refs source.locals target args values words rest
      ⟨by simpa [rest] using hinv, sourceRead, targetRead⟩
    apply wordMlInv_rearrange heap target.be a sp sp1 gens limit (holThe source.tstamps)
      conf source.refs _ _ ?_ added
    intro pair member
    have joined : pair ∈ joinEnv (sptFromList values) (sptToAList
        (sptInter (sptFromList2 (.loc l1 l2 :: words)) (adjustSet (sptFromList values)))) →
        pair ∈ values.zip words := callJoin_mem values words (.loc l1 l2) pair
    simp only [List.mem_append] at member ⊢
    simp only [rest, List.mem_append] at member ⊢
    tauto


end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
