module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Cons
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.MutCons

@[expose] public section

/-! Mutable constructor assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace MutConsWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end MutConsWitness

/-- Closed form of mutable-constructor application: space consumption, then fresh
reference allocation of the mutable block with its hole. Untagged proof infrastructure
for `assign_MutCons`. -/
theorem doApp_mutCons {C F : Type} (tag index : Nat) (values : List DataSem.Value)
    (source : DataSem.State C F) :
    DataSem.doApp (.memOp (.mutCons tag index)) values source =
      match DataSem.consumeSpace (values.length + 1) source, values[index]? with
      | some s1, some child =>
        .val (.refPtr false (DataSem.leastUnusedRef s1.refs),
          { s1 with
            refs := sptInsert (DataSem.leastUnusedRef s1.refs)
              (.mutBlock tag false (values.take index) child (values.drop (index + 1))) s1.refs
            safeForSpace := (DataSem.doStack (.memOp (.mutCons tag index)) values
              (DataSem.doLimSafe s1 (.memOp (.mutCons tag index)) values)).safeForSpace
            stackMax := (DataSem.doStack (.memOp (.mutCons tag index)) values
              (DataSem.doLimSafe s1 (.memOp (.mutCons tag index)) values)).stackMax })
      | _, _ => .err (.abort .typeError) := by
  cases h : DataSem.consumeSpace (values.length + 1) source with
  | none =>
    simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, h]
  | some s1 =>
    cases hi : values[index]? with
    | none =>
      simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, h,
        DataSem.doAppAux, DataSem.applyNonFfi, hi]
    | some child =>
      simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, h,
        DataSem.doAppAux, DataSem.applyNonFfi, hi, DataSem.doStack, DataSem.doLimSafe]

/-- A successful mutable-constructor application has no stack bound and is not safe
for space, since `allowed_op` excludes `MutCons`. Untagged proof infrastructure for
`assign_MutCons`. -/
theorem doApp_mutCons_unsafe {C F : Type} (tag index : Nat) (values : List DataSem.Value)
    (source result : DataSem.State C F) (value : DataSem.Value)
    (run : DataSem.doApp (.memOp (.mutCons tag index)) values source = .val (value, result)) :
    result.stackMax = none ∧ result.safeForSpace = false := by
  rw [doApp_mutCons] at run
  split at run
  · cases run
    simp [DataSem.doStack, DataSem.stackConsumed, DataSem.allowedOp]
  · cases run

/-- Mutable constructor assignment satisfies the original assignment simulation:
the generational collector, invalid headers and a missing hole all give up, which is
sound because the operation is never safe for space. The evaluator inherits the
real-model assumption documented in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_MutCons"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignMutCons_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ t k, op = .memOp (.mutCons t k))
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values)
    (depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r,
      WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q, r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace →
        stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  obtain ⟨tag, index, rfl⟩ := opIs
  have namesNone : names = none := by
    cases names <;> simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames ⊢
  subst names
  have cutSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
  subst cut
  obtain ⟨noMax, noSafe⟩ := doApp_mutCons_unsafe tag index values source resultState result run
  -- Every give-up branch is sound, since the operation is never safe for space.
  have giveUpOk : ∀ code : WordLangProgHOL (BitVec width),
      WordSemStateFiniteExact.evaluate code target =
        WordSemStateFiniteExact.evaluate (giveUp (width := width)) target →
      ∃ q r, WordSemStateFiniteExact.evaluate code target = (q, r) ∧
        (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
          (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
        (q ≠ some .notEnoughSpace →
          stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
    intro code codeEq
    obtain ⟨out, outEval, outFfi, targetFfi, _⟩ := evaluateGiveUp2 conf l1 l2 source target locs related
    refine ⟨some .notEnoughSpace, out, codeEq.trans outEval, ?_, ?_⟩
    · intro _
      exact ⟨outFfi.trans targetFfi.symm, by simp [noMax, optionLe], fun _ => noSafe⟩
    · simp
  have codeEq : compileAssign (width := width) conf n l dest (.memOp (.mutCons tag index)) args none =
      assignMutCons conf l dest tag args := rfl
  rw [codeEq]
  by_cases gen : ∃ gs, conf.gcKind = .generational gs
  · obtain ⟨gs, gcEq⟩ := gen
    apply giveUpOk
    simp [assignMutCons, gcEq]
  have codeCons : assignMutCons (width := width) conf l dest tag args = assignCons conf l dest tag args := by
    cases gcEq : conf.gcKind with
    | generational gs => exact absurd ⟨gs, gcEq⟩ gen
    | none => simp [assignMutCons, gcEq]
    | simple => simp [assignMutCons, gcEq]
  rw [codeCons]
  have gc : ∀ gs, conf.gcKind ≠ .generational gs := fun gs h => gen ⟨gs, h⟩
  cases args with
  | nil =>
    have valuesNil : values = [] := by simpa [DataSem.getVars] using argsEq.symm
    subst values
    rw [doApp_mutCons] at run
    split at run
    · rename_i hidx
      simp at hidx
    · cases run
  | cons first tail =>
    have argLen := DataSpace.getVars_length (first :: tail) source.locals values argsEq
    cases values with
    | nil => simp at argLen
    | cons v vs =>
      let vals := v :: vs
      let next := DataSem.doStack (.memOp (.mutCons tag index)) vals
        (DataSem.doLimSafe source (.memOp (.mutCons tag index)) vals)
      let key := DataSem.leastUnusedRef source.refs
      by_cases available : source.space < vals.length + 1
      · rw [doApp_mutCons] at run
        have av : source.space < vs.length + 1 + 1 := by simpa [vals] using available
        simp [DataSem.consumeSpace, av] at run
      have av : ¬ source.space < vs.length + 1 + 1 := by simpa [vals] using available
      cases hidx : vals[index]? with
      | none =>
        rw [doApp_mutCons] at run
        simp [DataSem.consumeSpace, av, show (v :: vs)[index]? = none from hidx] at run
      | some child =>
        have indexLt : index < vals.length := by
          by_contra h
          rw [List.getElem?_eq_none (by omega)] at hidx
          cases hidx
        have childEq : holEl index vals = child := by
          rw [holEl_eq_getElem index vals indexLt]
          simpa [List.getElem?_eq_getElem indexLt] using hidx
        let entry : BvlSem.Ref DataSem.Value :=
          .mutBlock tag false (vals.take index) child (vals.drop (index + 1))
        let refs := sptInsert key entry source.refs
        let midSource := {next with space := source.space - (vals.length + 1), refs := refs}
        have sourceRun : DataSem.doApp (.memOp (.mutCons tag index)) vals source =
            .val (.refPtr false key, midSource) := by
          rw [doApp_mutCons]
          simp [DataSem.consumeSpace, av, show (v :: vs)[index]? = some child from hidx, midSource,
            next, refs, entry, key, vals, DataSem.doStack, DataSem.doLimSafe]
        rw [show (v :: vs) = vals from rfl, sourceRun] at run
        simp only [SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        have nextRel : stateRel conf l1 l2 next target none locs :=
          stateRel_doStack conf l1 l2 _ target locs _ _
            (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
        cases header : encodeHeader (width := width) conf (4 * tag) (first :: tail).length with
        | none =>
          apply giveUpOk
          have header' : encodeHeader (width := width) conf (4 * tag) (tail.length + 1) = none := by
            simpa using header
          simp [assignCons, header']
        | some hd =>
          obtain ⟨words, getWords, lengthEq⟩ :=
            stateRel_getVars conf l1 l2 source target locs (first :: tail) (v :: vs) related argsEq
          let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
            flatStack source.stack target.stack
          let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
          have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
            target.store target.memory target.mdomain target envs (first :: tail) (v :: vs) words (by
              refine ⟨?_, argsEq, getWords⟩
              simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
          have fresh : ¬ sptMem key source.refs := by
            intro domain
            obtain ⟨value, found⟩ := (sptDomain_iff_lookup source.refs key).mp domain
            have no := DataSem.leastUnusedRef_unused source.refs
            rw [← show key = DataSem.leastUnusedRef source.refs from rfl, found] at no
            contradiction
          have memFact := memoryRel_mutCons conf target.be (holThe source.tstamps) source.refs
            source.space target.store target.memory target.mdomain (v :: vs) words (locals ++ envs)
            tag hd (by simpa [locals] using roots) lengthEq (by simp)
            (by simpa [← argLen, lengthEq] using header)
            (by simp only [vals] at available; simp only [List.length_cons] at available lengthEq; omega)
            related.2.2.2.2.2.2.1 index key indexLt fresh gc
          obtain ⟨free, curr, memory, freeLookup, currLookup, stored, outputHeap⟩ := memFact
          rw [show (v :: vs) = vals from rfl, childEq] at outputHeap
          let word := Build.makeConsPtr conf (free - curr) tag words.length
          let newStore := target.store.update (.nextFree,
            .word (free + wordSemBytesInWord * BitVec.ofNat width (words.length + 1)))
          let midTarget := {target with store := newStore, memory := memory}
          have baseHeap : memoryRel conf target.be (holThe source.tstamps) refs
              (source.space - (vals.length + 1)) newStore memory target.mdomain (locals ++ envs) := by
            apply memoryRel_rearrange conf target.be (holThe source.tstamps) refs _ newStore memory
              target.mdomain _ _ ?_ (by simpa [newStore, vals, lengthEq, refs, entry] using outputHeap)
            intro pair member
            exact List.mem_cons_of_mem _ member
          have midRel : stateRel conf l1 l2 midSource midTarget none locs := by
            rcases nextRel with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
              htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, _⟩
            refine ⟨hffi, hclock, hhandler, hgc, hcode, ?_, hgood, hshift, htstamp, ?_,
              hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, ?_, ?_⟩
            · simpa [midSource, midTarget, newStore, codeOracleRel, HolFiniteMapExact.update, FUPDATE] using horacle
            · simpa [midSource, midTarget, newStore, HolFiniteMapExact.update, FUPDATE] using hglobal
            · simpa [midSource, midTarget, newStore, HolFiniteMapExact.update, FUPDATE] using hlim
            · simpa [midSource, midTarget, newStore, next, DataSem.doStack, DataSem.doLimSafe,
                holFapply, HolFiniteMapExact.update, FUPDATE, locals, envs] using baseHeap
          let t1 := WordSemStateFiniteExact.setVar 1 (.word free) target
          let t3 := WordSemStateFiniteExact.setVar 3 (.word hd) t1
          let out := {t3 with memory := memory}
          have adjustedReads : WordSemStateFiniteExact.getVars ((first :: tail).map adjustVar) t3 = some words := by
            have read3 := getVarsAdjustVar (first :: tail) t1 t1.locals 3 (.word hd) (by decide)
            have read1 := getVarsAdjustVar (first :: tail) target target.locals 1 (.word free) (by decide)
            simpa [t3, t1, WordSemStateFiniteExact.setVar] using read3.trans (read1.trans getWords)
          have argsRead : WordSemStateFiniteExact.getVars (3 :: (first :: tail).map adjustVar) t3 = some (.word hd :: words) := by
            simp only [WordSemStateFiniteExact.getVars]
            have headRead : WordSemStateFiniteExact.getVar 3 t3 = some (.word hd) := by
              simp [WordSemStateFiniteExact.getVar, t3, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
            rw [headRead, adjustedReads]
          have baseRead : WordSemStateFiniteExact.getVar 1 t3 = some (.word free) := by
            simp [WordSemStateFiniteExact.getVar, t3, t1, WordSemStateFiniteExact.setVar,
              sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
          have storeEval := evaluate_storeEach (.word hd :: words) (3 :: (first :: tail).map adjustVar) t3 1 free memory
            ⟨by simpa [t3, t1, WordSemStateFiniteExact.setVar] using stored, argsRead, baseRead⟩
          have outRel : stateRel conf l1 l2 midSource
              {midTarget with locals := sptInsert 3 (.word hd) (sptInsert 1 (.word free) midTarget.locals)} none locs := by
            rw [stateRel_insert_3_1]
            exact midRel
          have finalOut := stateRel_insertRoot conf l1 l2 midSource
            {midTarget with locals := sptInsert 3 (.word hd) (sptInsert 1 (.word free) midTarget.locals)}
            locs dest (.refPtr false key) word outRel (by
              simpa [midSource, midTarget, newStore, next, DataSem.doStack, DataSem.doLimSafe,
                holFapply, HolFiniteMapExact.update, FUPDATE, locals, envs,
                vals, lengthEq, word, refs, entry, inter_insertOdd_adjustSet] using outputHeap)
          have shiftSmall : shiftLength conf - wordShiftAmount width < width := by
            have bound := related.2.2.2.2.2.2.2.1
            omega
          have widthBound : width < 2 ^ width := by
            rcases related.2.2.2.2.2.2.1 with h | h <;> subst width <;> decide
          have shiftMod : (shiftLength conf - wordShiftAmount width) % (2 ^ width) =
              shiftLength conf - wordShiftAmount width := Nat.mod_eq_of_lt (Nat.lt_trans shiftSmall widthBound)
          simp only [wordShiftAmount] at shiftSmall shiftMod
          have shiftNot : ¬ width ≤ shiftLength conf - (if width = 32 then 2 else 3) := Nat.not_le_of_gt shiftSmall
          have storeEvalNorm := storeEval
          simp only [t3, t1, WordSemStateFiniteExact.setVar] at storeEvalNorm
          have headerWords : encodeHeader (width := width) conf (4 * tag) words.length = some hd := by
            simpa [← argLen, lengthEq] using header
          refine ⟨none, WordSemStateFiniteExact.setStore .nextFree
            (.word (free + wordSemBytesInWord * BitVec.ofNat width (words.length + 1)))
            (WordSemStateFiniteExact.setVar (adjustVar dest) word out), ?_, ?_, ?_⟩
          · simp [assignCons, headerWords, wordListSeq, WordSemStateFiniteExact.evaluate,
              WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
              WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.getVar,
              WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock,
              freeLookup, t3, t1, out, word, shiftN, Build.makeConsPtr, wordShiftAmount,
              theWords, wordOpHOL, wordOp, ← argLen, lengthEq]
            simp only [BitVec.ofNat_eq_ofNat, List.map_cons] at storeEvalNorm
            rw [storeEvalNorm]
            have destNe : 1 ≠ adjustVar dest := by simp [adjustVar]
            simp [currLookup, sptLookup_sptInsert_same, BitVec.toNat_ofNat, shiftMod, shiftNot,
              wordShiftHOL, OrOp.or, sptLookup_sptInsert_ne, destNe, HolFiniteMapExact.updateEq,
              getLowerBits_ptrBits,
              BitVec.or_assoc, BitVec.or_comm]
            congr 2
            apply BitVec.eq_of_getLsbD_eq
            intro i hi
            simp [BitVec.getLsbD_or, Bool.or_left_comm]
          · simp
          · simpa [midSource, midTarget, newStore, out, t3, t1,
              WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar,
              HolFiniteMapExact.updateEq, HolFiniteMapExact.update, FUPDATE_HOL_eq_FUPDATE] using finalOut
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
