module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.RefSource
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.GiveUp
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.RefRead
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.RefMemory
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Update
public import Flapjack.FiniteMap.MapKeys
@[expose] public section

/-! Reference allocation in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

namespace RefAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end RefAssignmentWitness

/-- Reassemble the state relation after reference allocation; this is proof infrastructure
for `assign_Ref`, rather than a standalone HOL declaration. -/
private theorem stateRelRefStep {width : Nat} [NeZero width] {C F : Type}
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

/-- The safety premise supplies a reference header, as used in the HOL assignment proof.
This is proof infrastructure, rather than a standalone HOL declaration. -/
private theorem refHeaderOfSafe {width : Nat} [NeZero width] {C F : Type}
    (conf : DataToWord.Config) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (l1 l2 : Nat) (locs : List (Nat × Nat))
    (values : List DataSem.Value) (related : stateRel conf l1 l2 source target none locs)
    (safe : DataSem.limSafe source.limits (.memOp .ref) values) :
    ∃ hd, encodeHeader (width := width) conf 2 values.length = some hd := by
  have good := related.2.2.2.2.2.2.1
  have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have mem := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, _⟩ := mem
  have lenBound : conf.lenSize + 7 < width := heapMem.2.2.2.2.1
  have limitEq : source.limits.lengthLimit = conf.lenSize := limits.2.1
  have tagBound : 2 < 2 ^ (width - conf.lenSize - 2) := by
    have h : 2 ^ 3 ≤ 2 ^ (width - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have safeLen : values.length < 2 ^ conf.lenSize := by simpa [DataSem.limSafe, limitEq] using safe.1
  have wordBound : values.length < 2 ^ (width - 4) := by
    rcases good with h | h <;> subst width <;>
      simpa [DataSem.limSafe, DataSem.archSize, limits.2.2.1] using safe.2
  have tagSmall : 2 < 2 ^ width / 16 := by rcases good with h | h <;> subst width <;> decide
  refine ⟨makeHeader conf (BitVec.ofNat width 2) values.length, ?_⟩
  simp [encodeHeader, tagBound, tagSmall, wordBound, safeLen]

/-- Reference allocation satisfies the original data-to-word assignment goal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_Ref"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignRef_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F) (target : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .memOp .ref) (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values) (_depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r, WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q,r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace → stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  subst op
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    have argLen := DataSpace.getVars_length args source.locals values argsEq
    let next := DataSem.doStack (.memOp .ref) values (DataSem.doLimSafe source (.memOp .ref) values)
    let key := DataSem.leastUnusedRef source.refs
    by_cases available : source.space < values.length + 1
    · rw [doApp_ref] at run
      simp [DataSem.consumeSpace, available] at run
    · have sourceRun : DataSem.doApp (.memOp .ref) values source =
          .val (.refPtr true key, {next with
            refs := sptInsert key (.valueArray values) source.refs
            space := source.space - (values.length + 1)}) := by
        rw [doApp_ref]
        simp [DataSem.consumeSpace, available, next, key, DataSem.doStack, DataSem.doLimSafe]
      rw [sourceRun] at run
      cases run
      have nextRel : stateRel conf l1 l2 next target none locs :=
        stateRel_doStack conf l1 l2 _ target locs _ _
          (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
      cases header : encodeHeader (width := width) conf 2 args.length with
      | none =>
        obtain ⟨out, outEval, outFfi, targetFfi, outMax⟩ := evaluateGiveUp2 conf l1 l2 source target locs related
        have noSafe : ¬ DataSem.limSafe source.limits (.memOp .ref) values := by
          intro safe
          obtain ⟨hd, encoded⟩ := refHeaderOfSafe conf source target l1 l2 locs values related safe
          rw [argLen, header] at encoded
          contradiction
        refine ⟨some .notEnoughSpace, out, ?_, ?_, ?_⟩
        · simpa [compileAssign, assignRef, header] using outEval
        · intro _
          refine ⟨outFfi.trans targetFfi.symm, ?_, ?_⟩
          · have targetBound := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            exact BackendProps.optionLe_trans _ _ _ ⟨outMax, targetBound⟩
          · intro _
            simp [next, DataSem.doStack, DataSem.doLimSafe, noSafe]
        · simp
      | some hd =>
        obtain ⟨words, getWords, lengthEq⟩ :=
          stateRel_getVars conf l1 l2 source target locs args values related argsEq
        let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
          flatStack source.stack target.stack
        let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
        have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
          target.store target.memory target.mdomain target envs args values words (by
            refine ⟨?_, argsEq, getWords⟩
            simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
        have fresh : ¬ sptDomain source.refs key := by
          intro domain
          obtain ⟨value, found⟩ := (sptDomain_iff_lookup source.refs key).mp domain
          have no := DataSem.leastUnusedRef_unused source.refs
          rw [← show key = DataSem.leastUnusedRef source.refs from rfl, found] at no
          contradiction
        have memoryFact := memoryRel_ref (tagWidth := width) conf target.be (holThe source.tstamps) source.refs
          source.space target.store target.memory target.mdomain values words (locals ++ envs) hd key
          (by simpa [locals] using roots) lengthEq (by simpa [← argLen, lengthEq] using header)
          fresh (by omega) related.2.2.2.2.2.2.1
        obtain ⟨eoh, curr, trig, memory, endLookup, triggerLookup, currLookup, stored, outputHeap⟩ := memoryFact
        let addr := eoh - wordSemBytesInWord * BitVec.ofNat width (words.length + 1)
        let trig1 := trig - wordSemBytesInWord * BitVec.ofNat width (words.length + 1)
        let word := Build.makePtr conf (addr - curr) (0 : BitVec width) words.length
        let refs := sptInsert key (.valueArray values) source.refs
        let newStore := (target.store.update (.endOfHeap, .word addr)).update (.triggerGC, .word trig1)
        let midSource := {next with
          refs := refs
          space := source.space - (values.length + 1)}
        let midTarget := {target with store := newStore, memory := memory}
        have baseHeap : memoryRel conf target.be (holThe source.tstamps) refs
            (source.space - (values.length + 1)) newStore memory target.mdomain (locals ++ envs) := by
          apply memoryRel_rearrange conf target.be (holThe source.tstamps) refs _ newStore memory target.mdomain _ _ ?_
            (by simpa [addr, trig1, refs, newStore, lengthEq] using outputHeap)
          intro pair member
          exact List.mem_cons_of_mem _ member
        have midRel : stateRel conf l1 l2 midSource midTarget none locs := by
          apply stateRelRefStep conf l1 l2 next target locs refs (source.space - (values.length + 1)) addr trig1 memory nextRel
          simpa [next, DataSem.doStack, DataSem.doLimSafe, locals, envs, newStore] using baseHeap
        have finalRel := stateRel_insertRoot conf l1 l2 midSource midTarget locs dest (.refPtr true key) word midRel (by
          simpa [midSource, midTarget, next, DataSem.doStack, DataSem.doLimSafe, locals, envs, newStore, refs, addr, trig1, word, lengthEq, holFapply, HolFiniteMapExact.update, FUPDATE] using outputHeap)
        let preStore := {target with store := newStore}
        let t1 := WordSemStateFiniteExact.setVar 1 (.word addr) preStore
        let t3 := WordSemStateFiniteExact.setVar 3 (.word hd) t1
        let out := {t3 with memory := memory}
        have adjustedReads : WordSemStateFiniteExact.getVars (args.map adjustVar) t3 = some words := by
          have read3 := getVarsAdjustVar args t1 t1.locals 3 (.word hd) (by decide)
          have read1 := getVarsAdjustVar args preStore preStore.locals 1 (.word addr) (by decide)
          have readStore := getVarsWithStore (args.map adjustVar) target newStore
          simpa [t3, t1, preStore, WordSemStateFiniteExact.setVar] using read3.trans (read1.trans (readStore.trans getWords))
        have argsRead : WordSemStateFiniteExact.getVars (3 :: args.map adjustVar) t3 = some (.word hd :: words) := by
          simp only [WordSemStateFiniteExact.getVars]
          have headRead : WordSemStateFiniteExact.getVar 3 t3 = some (.word hd) := by
            simp [WordSemStateFiniteExact.getVar, t3, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
          rw [headRead, adjustedReads]
        have baseRead : WordSemStateFiniteExact.getVar 1 t3 = some (.word addr) := by
          simp [WordSemStateFiniteExact.getVar, t3, t1, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
        have storeEval := evaluate_storeEach (.word hd :: words) (3 :: args.map adjustVar) t3 1 addr memory
          ⟨by simpa [addr, t3, t1, preStore, WordSemStateFiniteExact.setVar] using stored, argsRead, baseRead⟩
        have storeSwap : (target.store.updateEq (.triggerGC, .word trig1)).updateEq (.endOfHeap, .word addr) = newStore := by
          apply HolFiniteMapExact.ext_lookup
          intro k
          cases k <;> simp [newStore, HolFiniteMapExact.updateEq, HolFiniteMapExact.update, FUPDATE_HOL, FUPDATE]
        have storeEvalRun : WordSemStateFiniteExact.evaluate (storeEach 1 (3 :: args.map adjustVar) 0)
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
        have finalOut := stateRel_insertRoot conf l1 l2 midSource out locs dest (.refPtr true key) word outRel (by
          simpa [out, t3, t1, preStore, WordSemStateFiniteExact.setVar, midSource, next, DataSem.doStack,
            DataSem.doLimSafe, locals, envs, newStore, refs, addr, trig1, word, lengthEq,
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
        have storeLookupEq := congrArg HolFiniteMapExact.lookup storeSwap
        simp only [addr, trig1, newStore, HolFiniteMapExact.updateEq, HolFiniteMapExact.update] at storeLookupEq
        have storeEvalNorm := storeEvalRun
        simp only [addr, trig1, out, t3, t1, preStore, newStore, WordSemStateFiniteExact.setVar,
          HolFiniteMapExact.updateEq, HolFiniteMapExact.update] at storeEvalNorm
        have headerWords : encodeHeader (width := width) conf 2 words.length = some hd := by
          simpa [← argLen, lengthEq] using header
        refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) word out, ?_, ?_, ?_⟩
        · simp [compileAssign, assignRef, headerWords, wordListSeq, WordSemStateFiniteExact.evaluate,
            WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
            WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.getVar,
            WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock,
            endLookup, triggerLookup, t3, t1, preStore, out, newStore, addr, trig1, word,
            shiftN, Build.makePtr, wordShiftAmount, theWords, wordOpHOL, wordOp,
            HolFiniteMapExact.update, HolFiniteMapExact.updateEq, FUPDATE_HOL, sptLookup_sptInsert_same, ← argLen, lengthEq]
          simp only [BitVec.ofNat_eq_ofNat] at storeEvalNorm
          rw [storeEvalNorm]
          simp [currLookup, FUPDATE_HOL, sptLookup_sptInsert_same,
            BitVec.toNat_ofNat, shiftMod, shiftNot, wordShiftHOL, OrOp.or, BitVec.or_zero,
            sptLookup_sptInsert_ne, storeLookupEq]
        · simp
        · simpa [midSource, refs] using finalOut

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
