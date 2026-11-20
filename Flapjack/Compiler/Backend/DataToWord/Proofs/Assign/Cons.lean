module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Const
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.GiveUp
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StateTstamps
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StoreEach
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.RefRead
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MemoryRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateInsert
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConsMemory
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Unit

@[expose] public section

/-! Constructor assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace ConsWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end ConsWitness

/-- Constructor assignment satisfies the original assignment simulation, including
invalid headers and allocation of nonempty constructors. The evaluator inherits
the real-model assumption documented in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_Cons"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignCons_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ tag, op = .blockOp (.cons tag))
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
  obtain ⟨tag, rfl⟩ := opIs
  have namesNone : names = none := by
    cases names <;> simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames ⊢
  subst names
  have cutSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
  subst cut
  have hasStamp := stateRel_imp_tstamps conf l1 l2 source target none locs related
  cases args with
  | nil =>
    have valuesNil : values = [] := by simpa [DataSem.getVars] using argsEq.symm
    subst values
    simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.doAppAux, DataSem.applyNonFfi] at run
    obtain ⟨rfl, rfl⟩ := run
    let next := DataSem.doStack (.blockOp (.cons tag)) []
      (DataSem.doLimSafe source (.blockOp (.cons tag)) [])
    have nextRel : stateRel conf l1 l2 next target none locs :=
      stateRel_doStack conf l1 l2 _ target locs _ _
        (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
    have good := related.2.2.2.2.2.2.1
    by_cases bound : tag < 2 ^ width / 16
    · have imm : (blockNil tag : BitVec width) = BitVec.ofNat width (16 * tag + 2) := by
        rcases good with hw | hw <;> subst width <;> apply BitVec.eq_of_toNat_eq <;>
          simp [blockNil, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
            Nat.shiftLeft_eq, Nat.mul_mod, Nat.add_mod, Nat.mul_comm]
      have root := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have withRoot := memoryRel_consEmpty conf target.be (holThe next.tstamps) next.refs next.space
        target.store target.memory target.mdomain _ tag ⟨root, bound, good⟩
      have final := stateRel_insertRoot conf l1 l2 next target locs dest (.block 0 tag [])
        (.word (BitVec.ofNat width (16 * tag + 2))) nextRel (by simpa [imm] using withRoot)
      refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest)
        (.word (BitVec.ofNat width (16 * tag + 2))) target, ?_, ?_, ?_⟩
      · simp [compileAssign, assignCons, bound, WordSemStateFiniteExact.evaluate,
          WordSemStateFiniteExact.wordExp]
      · simp
      · simpa [next] using final
    · obtain ⟨out, outEval, outFfi, targetFfi, outMax⟩ :=
        evaluateGiveUp2 conf l1 l2 source target locs related
      refine ⟨some .notEnoughSpace, out, ?_, ?_, ?_⟩
      · simpa [compileAssign, assignCons, bound] using outEval
      · intro _
        refine ⟨outFfi.trans targetFfi.symm, ?_, ?_⟩
        · exact BackendProps.optionLe_trans _ _ _ ⟨outMax, nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
        · intro _
          have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have arch : DataSem.archSize source.limits = width := by
            rcases good with h | h <;> subst width <;>
              simp [DataSem.archSize, limits.2.2.1]
          simp [DataSem.doStack, DataSem.doLimSafe, DataSem.limSafe, arch, bound]
      · simp
  | cons first tail =>
    have argLen := DataSpace.getVars_length (first :: tail) source.locals values argsEq
    cases values with
    | nil => simp at argLen
    | cons v vs =>
      let vals := v :: vs
      let next := DataSem.doStack (.blockOp (.cons tag)) vals
        (DataSem.doLimSafe source (.blockOp (.cons tag)) vals)
      by_cases available : source.space < vals.length + 1
      · have av : source.space ≤ vs.length + 1 := by dsimp [vals] at available; simp at available; omega
        simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.consumeSpace, av] at run
      · have av : ¬ source.space ≤ vs.length + 1 := by dsimp [vals] at available; simp at available; omega
        obtain ⟨timestamp, timestampEq⟩ := hasStamp
        have sourceRun : DataSem.doApp (.blockOp (.cons tag)) vals source =
            .val (.block timestamp tag vals, {next with
              tstamps := some (timestamp + 1), space := source.space - (vals.length + 1),
              safeForSpace := decide (vals.length < 2 ^ source.limits.lengthLimit) && next.safeForSpace}) := by
          simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.consumeSpace, av, DataSem.doAppAux, DataSem.applyNonFfi,
            DataSem.withFreshTimestamp, timestampEq, DataSem.checkLim, next, vals,
            DataSem.doStack, DataSem.doLimSafe]
        rw [sourceRun] at run
        cases run
        have nextRel : stateRel conf l1 l2 next target none locs :=
          stateRel_doStack conf l1 l2 _ target locs _ _
            (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
        cases header : encodeHeader (width := width) conf (4 * tag) (first :: tail).length with
        | none =>
          obtain ⟨out, outEval, outFfi, targetFfi, outMax⟩ :=
            evaluateGiveUp2 conf l1 l2 source target locs related
          have noSafe : ¬ DataSem.limSafe source.limits (.blockOp (.cons tag)) vals := by
            intro safe
            have good := related.2.2.2.2.2.2.1
            have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            have arch : DataSem.archSize source.limits = width := by
              rcases good with h | h <;> subst width <;>
                simp [DataSem.archSize, limits.2.2.1]
            have lenEq : source.limits.lengthLimit = conf.lenSize := limits.2.1
            simp only [DataSem.limSafe, vals, List.cons_ne_nil, ↓reduceIte] at safe
            have tagSmall : 4 * tag < 2 ^ width / 16 := by simpa [arch] using safe.2.2.1
            have tagBound : 4 * tag < 2 ^ (width - conf.lenSize - 2) := by
              simpa [arch, lenEq] using safe.2.2.2
            have lenBound : (first :: tail).length < 2 ^ conf.lenSize := by
              simpa [lenEq, ← argLen] using safe.1
            have wordBound : (first :: tail).length < 2 ^ (width - 4) := by
              simpa [arch, ← argLen] using safe.2.1
            simp only [List.length_cons] at lenBound wordBound header
            simp [encodeHeader, tagSmall, tagBound, lenBound, wordBound] at header
          refine ⟨some .notEnoughSpace, out, ?_, ?_, ?_⟩
          · have header' : encodeHeader (width := width) conf (4 * tag) (tail.length + 1) = none := by
              simpa using header
            simpa [compileAssign, assignCons, header'] using outEval
          · intro _
            refine ⟨outFfi.trans targetFfi.symm, ?_, ?_⟩
            · exact BackendProps.optionLe_trans _ _ _
                ⟨outMax, nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
            · intro _
              simp [next, DataSem.doStack, DataSem.doLimSafe, noSafe]
          · simp
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
          have memFact := memoryRel_cons1 conf target.be (holThe source.tstamps) source.refs
            source.space target.store target.memory target.mdomain (v :: vs) words (locals ++ envs)
            tag hd (by simpa [locals] using roots) lengthEq (by simp)
            (by simpa [← argLen, lengthEq] using header) (by simp only [vals] at available; simp only [List.length_cons] at available lengthEq; omega)
            related.2.2.2.2.2.2.1
          obtain ⟨free, curr, memory, freeLookup, currLookup, stored, outputHeap⟩ := memFact
          let word := Build.makeConsPtr conf (free - curr) tag words.length
          let newStore := target.store.update (.nextFree,
            .word (free + wordSemBytesInWord * BitVec.ofNat width (words.length + 1)))
          let midSource := {next with
            tstamps := some (timestamp + 1),
            space := source.space - (vals.length + 1),
            safeForSpace := decide (vals.length < 2 ^ source.limits.lengthLimit) && next.safeForSpace}
          let midTarget := {target with store := newStore, memory := memory}
          have baseHeap : memoryRel conf target.be (timestamp + 1) source.refs
              (source.space - (vals.length + 1)) newStore memory target.mdomain (locals ++ envs) := by
            apply memoryRel_rearrange conf target.be (timestamp + 1) source.refs _ newStore memory target.mdomain _ _ ?_
              (by simpa [timestampEq, holThe, newStore, vals, lengthEq] using outputHeap)
            intro pair member
            exact List.mem_cons_of_mem _ member
          have midRel : stateRel conf l1 l2 midSource midTarget none locs := by
            rcases nextRel with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
              htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, _⟩
            refine ⟨hffi, hclock, hhandler, hgc, hcode, ?_, hgood, hshift, by simp [midSource], ?_,
              hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, ?_, ?_⟩
            · simpa [midSource, midTarget, newStore, codeOracleRel, HolFiniteMapExact.update, FUPDATE] using horacle
            · simpa [midSource, midTarget, newStore, HolFiniteMapExact.update, FUPDATE] using hglobal
            · simpa [midSource, midTarget, newStore, HolFiniteMapExact.update, FUPDATE] using hlim
            · simpa [midSource, midTarget, newStore, next, DataSem.doStack, DataSem.doLimSafe,
                holFapply, HolFiniteMapExact.update, FUPDATE, locals, envs, holThe] using baseHeap
          have finalRel := stateRel_insertRoot conf l1 l2 midSource midTarget locs dest
            (.block timestamp tag vals) word midRel (by
              simpa [midSource, midTarget, newStore, next, DataSem.doStack, DataSem.doLimSafe,
                holFapply, HolFiniteMapExact.update, FUPDATE, locals, envs, holThe, timestampEq,
                vals, lengthEq, word] using outputHeap)
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
            locs dest (.block timestamp tag vals) word outRel (by
              simpa [midSource, midTarget, newStore, next, DataSem.doStack, DataSem.doLimSafe,
                holFapply, HolFiniteMapExact.update, FUPDATE, locals, envs, holThe, timestampEq,
                vals, lengthEq, word, inter_insertOdd_adjustSet] using outputHeap)
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
          · simp [compileAssign, assignCons, headerWords, wordListSeq, WordSemStateFiniteExact.evaluate,
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
