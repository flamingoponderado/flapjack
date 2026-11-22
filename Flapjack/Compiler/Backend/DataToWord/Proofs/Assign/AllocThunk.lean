module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Ref
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.DoAppLemmas
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.AllocThunk
@[expose] public section

/-! Thunk allocation in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

namespace AllocThunkAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end AllocThunkAssignmentWitness

/-- Reassemble the state relation after heap allocation; local proof infrastructure
for `assign_AllocThunk`, rather than a standalone HOL declaration. -/
private theorem stateRelAllocThunkStep {width : Nat} [NeZero width] {C F : Type}
    (conf : DataToWord.Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat) (eoh trig : BitVec width)
    (memory : BitVec width → WordLocW width)
    (related : stateRel conf l1 l2 source target none locs)
    (heap : memoryRel conf target.be (holThe source.tstamps) refs space
      ((target.store.update (.endOfHeap, .word eoh)).update (.triggerGC, .word trig)) memory target.mdomain
      (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)) :
    stateRel conf l1 l2 {source with refs := refs, space := space}
      {target with store := (target.store.update (.endOfHeap, .word eoh)).update (.triggerGC, .word trig), memory := memory} none locs := by
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, _⟩
  refine ⟨hffi, hclock, hhandler, hgc, hcode, ?_, hgood, hshift, htstamp, ?_, hzero,
    hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, ?_, ?_⟩
  · simpa [codeOracleRel, HolFiniteMapExact.update, FUPDATE] using horacle
  · simpa [HolFiniteMapExact.update, FUPDATE] using hglobal
  · simpa [HolFiniteMapExact.update, FUPDATE] using hlim
  · simpa [holFapply, HolFiniteMapExact.update, FUPDATE] using heap

/-- Both thunk headers (tags 6 and 14, one payload word) are always encodable under
the state relation, as in HOL's `encode_header_def` contradiction; local proof
infrastructure for `assign_AllocThunk`. -/
private theorem allocThunkHeaderSome {width : Nat} [NeZero width] {C F : Type}
    (conf : DataToWord.Config) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (l1 l2 : Nat) (locs : List (Nat × Nat))
    (related : stateRel conf l1 l2 source target none locs) (mode : AstHOL.ThunkMode) :
    ∃ hd, encodeHeader (width := width) conf
      (match mode with | .evaluated => 14 | .notEvaluated => 6) 1 = some hd := by
  have good := related.2.2.2.2.2.2.1
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, _⟩ := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have lenPos : 0 < conf.lenSize := by
    have h := heapMem.2.2.2.1
    omega
  have lenBound : conf.lenSize + 7 < width := heapMem.2.2.2.2.1
  have countBound : 1 < 2 ^ conf.lenSize := by
    have h : 2 ^ 1 ≤ 2 ^ conf.lenSize := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rcases good with h | h <;> subst width <;> cases mode
  · refine ⟨makeHeader conf (BitVec.ofNat 32 14) 1, ?_⟩
    simp [encodeHeader, countBound, show 14 < 2 ^ (32 - conf.lenSize - 2) by
      have h : 2 ^ 4 ≤ 2 ^ (32 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega]
  · refine ⟨makeHeader conf (BitVec.ofNat 32 6) 1, ?_⟩
    simp [encodeHeader, countBound, show 6 < 2 ^ (32 - conf.lenSize - 2) by
      have h : 2 ^ 4 ≤ 2 ^ (32 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega]
  · refine ⟨makeHeader conf (BitVec.ofNat 64 14) 1, ?_⟩
    simp [encodeHeader, countBound, show 14 < 2 ^ (64 - conf.lenSize - 2) by
      have h : 2 ^ 4 ≤ 2 ^ (64 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega]
  · refine ⟨makeHeader conf (BitVec.ofNat 64 6) 1, ?_⟩
    simp [encodeHeader, countBound, show 6 < 2 ^ (64 - conf.lenSize - 2) by
      have h : 2 ^ 4 ≤ 2 ^ (64 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega]

open Classical in
/-- Thunk allocation satisfies the original data-to-word assignment goal. The evaluator
inherits the real-model assumption documented in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_AllocThunk"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignAllocThunk_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ ev, op = .thunkOp (.allocThunk ev))
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values)
    (_depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r,
      WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q, r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace →
        stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  obtain ⟨mode, rfl⟩ := opIs
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    obtain ⟨v, rfl⟩ : ∃ v, values = [v] := by
      cases values with
      | nil =>
        simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi] at run
        split at run <;> simp at run
      | cons v vs =>
        cases vs with
        | nil => exact ⟨v, rfl⟩
        | cons x xs =>
          simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset,
            DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi] at run
          split at run <;> simp at run
    have argLen : args.length = 1 := by
      have h := DataSpace.getVars_length args source.locals [v] argsEq
      simpa using h.symm
    obtain ⟨a, rfl⟩ : ∃ a, args = [a] := by
      match args, argLen with
      | [a], _ => exact ⟨a, rfl⟩
    let next := DataSem.doStack (.thunkOp (.allocThunk mode)) [v]
      (DataSem.doLimSafe source (.thunkOp (.allocThunk mode)) [v])
    let key := DataSem.leastUnusedRef source.refs
    by_cases available : source.space < 1 + 1
    · rw [doApp_allocThunk] at run
      simp [DataSem.consumeSpace, available] at run
    by_cases bad : DataSem.badThunkUpdate mode v source.refs
    · rw [doApp_allocThunk] at run
      simp [DataSem.consumeSpace, available, bad] at run
    have sourceRun : DataSem.doApp (.thunkOp (.allocThunk mode)) [v] source =
        .val (.refPtr false key, {next with
          refs := sptInsert key (.thunk mode v) source.refs
          space := source.space - (1 + 1)}) := by
      rw [doApp_allocThunk]
      simp [DataSem.consumeSpace, available, bad, next, key, DataSem.doStack, DataSem.doLimSafe]
    rw [sourceRun] at run
    cases run
    have nextRel : stateRel conf l1 l2 next target none locs :=
      stateRel_doStack conf l1 l2 _ target locs _ _
        (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
    obtain ⟨hd, header⟩ := allocThunkHeaderSome conf source target l1 l2 locs related mode
    obtain ⟨words, getWords, lengthEq⟩ :=
      stateRel_getVars conf l1 l2 source target locs [a] [v] related argsEq
    obtain ⟨w, rfl⟩ : ∃ w, words = [w] := by
      match words, lengthEq with
      | [w], _ => exact ⟨w, rfl⟩
    let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
      flatStack source.stack target.stack
    let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
    have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
      target.store target.memory target.mdomain target envs [a] [v] [w] (by
        refine ⟨?_, argsEq, getWords⟩
        simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    have fresh : ¬ sptDomain source.refs key := by
      intro domain
      obtain ⟨value, found⟩ := (sptDomain_iff_lookup source.refs key).mp domain
      have no := DataSem.leastUnusedRef_unused source.refs
      rw [← show key = DataSem.leastUnusedRef source.refs from rfl, found] at no
      contradiction
    have notThunk : mode = .evaluated → DataSem.destThunk v source.refs = .notThunk := by
      intro evaluated
      by_contra hne
      exact bad ⟨evaluated, hne⟩
    have memoryFact := memoryRel_allocThunk (tagWidth := width) conf target.be (holThe source.tstamps)
      source.refs source.space target.store target.memory target.mdomain v w (locals ++ envs) mode hd key
      ⟨by simpa [locals] using roots, header, fresh, notThunk, by omega, related.2.2.2.2.2.2.1⟩
    obtain ⟨eoh, curr, trig, memory, endLookup, triggerLookup, currLookup, stored, outputHeap⟩ := memoryFact
    let addr := eoh - wordSemBytesInWord * 2
    let trig1 := trig - wordSemBytesInWord * 2
    let word := Build.makePtr conf (addr - curr) (0 : BitVec width) 1
    let refs := sptInsert key (.thunk mode v) source.refs
    let newStore := (target.store.update (.endOfHeap, .word addr)).update (.triggerGC, .word trig1)
    let midSource := {next with
      refs := refs
      space := source.space - (1 + 1)}
    let midTarget := {target with store := newStore, memory := memory}
    have baseHeap : memoryRel conf target.be (holThe source.tstamps) refs
        (source.space - (1 + 1)) newStore memory target.mdomain (locals ++ envs) := by
      apply memoryRel_rearrange conf target.be (holThe source.tstamps) refs _ newStore memory target.mdomain _ _ ?_
        (by simpa [addr, trig1, refs, newStore] using outputHeap)
      intro pair member
      exact List.mem_cons_of_mem _ member
    have midRel : stateRel conf l1 l2 midSource midTarget none locs := by
      apply stateRelAllocThunkStep conf l1 l2 next target locs refs (source.space - (1 + 1)) addr trig1 memory nextRel
      simpa [next, DataSem.doStack, DataSem.doLimSafe, locals, envs, newStore] using baseHeap
    let preStore := {target with store := newStore}
    let t1 := WordSemStateFiniteExact.setVar 1 (.word addr) preStore
    let t3 := WordSemStateFiniteExact.setVar 3 (.word hd) t1
    let out := {t3 with memory := memory}
    have adjustedReads : WordSemStateFiniteExact.getVars ([a].map adjustVar) t3 = some [w] := by
      have read3 := getVarsAdjustVar [a] t1 t1.locals 3 (.word hd) (by decide)
      have read1 := getVarsAdjustVar [a] preStore preStore.locals 1 (.word addr) (by decide)
      have readStore := getVarsWithStore ([a].map adjustVar) target newStore
      simpa [t3, t1, preStore, WordSemStateFiniteExact.setVar] using read3.trans (read1.trans (readStore.trans getWords))
    have argsRead : WordSemStateFiniteExact.getVars [3, adjustVar a] t3 = some [.word hd, w] := by
      have headRead : WordSemStateFiniteExact.getVar 3 t3 = some (.word hd) := by
        simp [WordSemStateFiniteExact.getVar, t3, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
      have rest : WordSemStateFiniteExact.getVars [adjustVar a] t3 = some [w] := by simpa using adjustedReads
      simp only [WordSemStateFiniteExact.getVars] at rest ⊢
      rw [headRead]
      cases h : WordSemStateFiniteExact.getVar (adjustVar a) t3 <;> simp_all
    have baseRead : WordSemStateFiniteExact.getVar 1 t3 = some (.word addr) := by
      simp [WordSemStateFiniteExact.getVar, t3, t1, WordSemStateFiniteExact.setVar,
        sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
    have storeEval := evaluate_storeEach [.word hd, w] [3, adjustVar a] t3 1 addr memory
      ⟨by simpa [addr, t3, t1, preStore, WordSemStateFiniteExact.setVar] using stored, argsRead, baseRead⟩
    have storeSwap : (target.store.updateEq (.triggerGC, .word trig1)).updateEq (.endOfHeap, .word addr) = newStore := by
      apply HolFiniteMapExact.ext_lookup
      intro k
      cases k <;> simp [newStore, HolFiniteMapExact.updateEq, HolFiniteMapExact.update, FUPDATE_HOL, FUPDATE]
    have storeEvalRun : WordSemStateFiniteExact.evaluate (storeEach 1 [3, adjustVar a] 0)
        {target with locals := sptInsert 3 (.word hd) (sptInsert 1 (.word addr) target.locals)
                     store := (target.store.updateEq (.triggerGC, .word trig1)).updateEq (.endOfHeap, .word addr)} =
          (none, {out with store := (target.store.updateEq (.triggerGC, .word trig1)).updateEq (.endOfHeap, .word addr)}) := by
      simpa [out, t3, t1, preStore, WordSemStateFiniteExact.setVar, storeSwap] using storeEval
    have outRel : stateRel conf l1 l2 midSource out none locs := by
      have updated : stateRel conf l1 l2 midSource
          {midTarget with locals := sptInsert 3 (.word hd) (sptInsert 1 (.word addr) midTarget.locals)} none locs := by
        rw [stateRel_insert_3_1]
        exact midRel
      simpa [out, t3, t1, preStore, midTarget, WordSemStateFiniteExact.setVar] using updated
    have finalOut := stateRel_insertRoot conf l1 l2 midSource out locs dest (.refPtr false key) word outRel (by
      simpa [out, t3, t1, preStore, WordSemStateFiniteExact.setVar, midSource, next, DataSem.doStack,
        DataSem.doLimSafe, locals, envs, newStore, refs, addr, trig1, word,
        holFapply, HolFiniteMapExact.update, FUPDATE, inter_insertOdd_adjustSet] using outputHeap)
    have shiftSmall : shiftLength conf - wordShiftAmount width < width := by
      have bound := related.2.2.2.2.2.2.2.1
      omega
    have widthBound : width < 2 ^ width := by
      rcases related.2.2.2.2.2.2.1 with h | h <;> subst width <;> decide
    have shiftMod : (shiftLength conf - wordShiftAmount width) % (2 ^ width) =
        shiftLength conf - wordShiftAmount width := Nat.mod_eq_of_lt (Nat.lt_trans shiftSmall widthBound)
    simp only [wordShiftAmount] at shiftSmall shiftMod
    have shiftNot : ¬ width ≤ shiftLength conf - (if width = 32 then 2 else 3) := Nat.not_le_of_gt shiftSmall
    have storeEvalNorm := storeEvalRun
    simp only [addr, trig1, out, t3, t1, preStore, newStore, WordSemStateFiniteExact.setVar,
      HolFiniteMapExact.updateEq, HolFiniteMapExact.update] at storeEvalNorm
    refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) word out, ?_, ?_, ?_⟩
    · simp only [compileAssign, arg1, assignAllocThunk]
      split
      · rename_i none2
        exfalso
        cases mode <;> simp only at none2 header <;> rw [none2] at header <;> cases header
      rename_i hd2 some2
      have hdEq : hd2 = hd := by
        cases mode <;> simp only at some2 header <;> rw [some2] at header <;> exact Option.some.inj header
      subst hdEq
      simp [wordListSeq, WordSemStateFiniteExact.evaluate,
        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
        WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.getVar,
        WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock,
        endLookup, triggerLookup, t3, t1, preStore, out, newStore, addr, trig1, word,
        shiftN, Build.makePtr, wordShiftAmount, theWords, wordOpHOL, wordOp,
        HolFiniteMapExact.update, HolFiniteMapExact.updateEq, FUPDATE_HOL, sptLookup_sptInsert_same]
      simp only [BitVec.ofNat_eq_ofNat] at storeEvalNorm
      rw [storeEvalNorm]
      simp [currLookup, FUPDATE_HOL, sptLookup_sptInsert_same,
        BitVec.toNat_ofNat, shiftMod, shiftNot, wordShiftHOL, OrOp.or, BitVec.or_zero,
        sptLookup_sptInsert_ne]
      funext k
      cases k <;> simp [FUPDATE_HOL, FUPDATE]
    · simp
    · simpa [midSource, refs] using finalOut

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
