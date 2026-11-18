module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PopEnvSetVar
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackSplit
public import Flapjack.Compiler.Backend.Semantics.DataProps.Jump
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateLaws

@[expose] public section

/-! Exception-jump simulation for related data and word states. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace jumpExcStateMap
/-- Canonical target-state roundtrip for exception-jump simulation. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end jumpExcStateMap

/-- Translate the option-add expression used by the stack bound. -/
private theorem optionMapAdd (a b : Option Nat) :
    Option.map₂ (· + ·) a b = wordSemOptionAdd a b := by
  cases a <;> cases b <;> rfl

/-- An exception jump and variable restoration have a matching target jump. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_jump_exc"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_jumpExc {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat) (source source' : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (n : Nat) (value : Flapjack.Compiler.Backend.DataSem.Value) (word : WordLocW width)
    (premises : stateRel conf l1 l2 source target none locs ∧
      DataSem.getVar n source.locals = some value ∧
      WordSemStateFiniteExact.getVar (adjustVar n) target = some word ∧
      DataSem.jumpExc source = some source') :
    ∃ target' d1 d2 l5 l6 rest,
      WordSemStateFiniteExact.jumpExc target = some (target', d1, d2) ∧
      wordSemLastN (source'.stack.length + 1) locs = (l5,l6) :: rest ∧
      ∀ i, stateRel conf l5 l6 (DataSem.setVar i value source')
        (WordSemStateFiniteExact.setVar (adjustVar i) word target') none rest := by
  obtain ⟨related, sourceFound, targetFound, run⟩ := premises
  obtain ⟨bound, handler, env, size, frames, sourceSuffix, sourceEq⟩ :=
    DataSem.jumpExcImp source source' run
  have hstacks := related.2.2.2.2.2.2.2.2.2.2.2.2.1
  have locRel := related.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have handlerEq := related.2.2.1
  have lenEq := hstacks.length_eq
  obtain ⟨targetFrame, targetFrames, targetSuffix, frameRel, tailRel⟩ :=
    lastn_list_rel_lemma source.stack target.stack frames (source.handler + 1) () ()
      (.exc size env handler) stackRel ⟨sourceSuffix, hstacks⟩
  obtain ⟨location, locationRest, locationSuffix, locHead, locTail⟩ :=
    lastn_list_rel_lemma target.stack locs targetFrames (source.handler + 1) () ()
      targetFrame containsLoc ⟨targetSuffix, locRel⟩
  obtain ⟨l5,l6⟩ := location
  have sizeSuffix := lastn_cons_imp_length source.stack (source.handler + 1)
    (.exc size env handler) frames (by omega) sourceSuffix
  have countEq : source'.stack.length + 1 = source.handler + 1 := by
    rw [sourceEq]
    simpa using sizeSuffix
  have targetBound' : source.handler < target.stack.length := by omega
  cases targetFrame with
  | stackFrame targetSize nonGc gc targetHandler =>
    cases targetHandler with
    | none => simp [stackRel] at frameRel
    | some triple =>
      obtain ⟨nextHandler,d1,d2⟩ := triple
      change stackEnvRel size targetSize env nonGc gc ∧ nextHandler = handler at frameRel
      obtain ⟨⟨gcKeys, sizeEq, nonGcKeys, gcDistinct, lookupRel⟩, rfl⟩ := frameRel
      obtain ⟨sourcePrefix, sourceAppend, _⟩ := lastn_imp_append source.stack (source.handler + 1)
        (.exc size env nextHandler :: frames) ⟨by omega, sourceSuffix⟩
      obtain ⟨targetPrefix, targetAppend, _⟩ := lastn_imp_append target.stack (source.handler + 1)
        (.stackFrame targetSize nonGc gc (some (nextHandler,d1,d2)) :: targetFrames)
        ⟨by omega, targetSuffix⟩
      have prefixLen : sourcePrefix.length = targetPrefix.length := by
        have tailsLen := tailRel.length_eq
        simp only [sourceAppend, targetAppend, List.length_append, List.length_cons] at lenEq
        omega
      have originalRoot : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
          target.store target.memory target.mdomain
          ((value, word) :: joinEnv source.locals
            (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
            [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack) := by
        rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmem⟩
        obtain ⟨heap, limit, a, sp, sp1, gens, hstore, hinv, hbound, hspace⟩ := hmem
        refine ⟨heap, limit, a, sp, sp1, gens, hstore, ?_, hbound, hspace⟩
        let rest := [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
        have added := wordMlInv_lookup heap target.be a sp sp1 gens limit (holThe source.tstamps)
          conf source.refs [] rest source.locals target.locals n value word
          ⟨by simpa [rest] using hinv, sourceFound, targetFound⟩
        simpa [rest] using added
      have restoredRoot : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
          target.store target.memory target.mdomain
          ((value, word) :: joinEnv env (sptToAList
            (sptInter (sptUnion (sptFromAList gc) (sptFromAList nonGc)) (adjustSet env))) ++
            [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack frames targetFrames) := by
        rw [sourceAppend, targetAppend, flatStack_append sourcePrefix targetPrefix _ _ prefixLen] at originalRoot
        simp only [flatStack] at originalRoot
        apply memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
          target.store target.memory target.mdomain _ _ ?_ originalRoot
        intro pair member
        have joined : pair ∈ joinEnv env (sptToAList
            (sptInter (sptUnion (sptFromAList gc) (sptFromAList nonGc)) (adjustSet env))) →
            pair ∈ joinEnv env gc := restored_join_mem env nonGc gc pair nonGcKeys
        simp only [List.mem_cons, List.mem_append] at member ⊢
        tauto
      refine ⟨{target with handler := nextHandler, locals := sptUnion (sptFromAList gc) (sptFromAList nonGc), stack := targetFrames, localsSize := targetSize}, d1,d2,l5,l6,locationRest, ?_, ?_, ?_⟩
      · simp [WordSemStateFiniteExact.jumpExc, handlerEq, targetBound', targetSuffix]
      · simpa [countEq] using locationSuffix
      · intro i
        rw [sourceEq]
        apply stateRel_insertRoot conf l5 l6 _ _ locationRest i value word
        · rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
            htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
          refine ⟨hffi, hclock, rfl, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
            ?_, ?_, tailRel, locTail, ?_, hmax, hsizes, ?_, hlim, ?_⟩
          · intro _
            have gcZero : sptAListLookup 0 gc = none := by
              cases found : sptAListLookup 0 gc with
              | none => rfl
              | some v =>
                have member := sptAListLookup_mem 0 gc v found
                exact ((gcKeys (0,v) member).1 rfl).elim
            change sptAListLookup 0 nonGc = some (.loc l5 l6) at locHead
            simp [sptLookup_sptUnion, sptLookup_sptFromAList, gcZero, locHead]
          · intro key present
            have found := (lookupRel key).mp present
            obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp found
            simp [sptLookup_sptUnion, hv]
          · change optionLe (Option.map₂ (· + ·) (wordSemStackSize targetFrames) targetSize) target.stackMax
            rw [optionMapAdd]
            apply optionLe_tail targetSize nonGc gc (some (nextHandler,d1,d2)) targetFrames target.localsSize target.stackMax
            rw [optionMapAdd] at hacc
            have hle := optionLe_stackSize_append targetPrefix
              (.stackFrame targetSize nonGc gc (some (nextHandler,d1,d2)) :: targetFrames)
            rw [← targetAppend] at hle
            have addLe := optionLe_optionAdd_mono_right (c := target.localsSize) hle
            rw [wordSemOptionAdd_comm target.localsSize _, wordSemOptionAdd_comm target.localsSize _] at addLe
            exact BackendProps.optionLe_trans _ _ _ ⟨addLe, hacc⟩
          · exact sizeEq.symm
          · simpa using memoryRel_tl conf target.be (holThe source.tstamps) source.refs source.space
              target.store target.memory target.mdomain (value,word) _ restoredRoot
        · simpa using restoredRoot


end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
