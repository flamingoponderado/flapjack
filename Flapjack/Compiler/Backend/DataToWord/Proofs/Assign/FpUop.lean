module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.FpCommon
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.RealAddress
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Space
@[expose] public section

/-! Unary floating-point assignment correctness for data-to-word compilation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

namespace FpUopAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end FpUopAssignmentWitness

/-- Invert source unary FP application for the assignment proof; this is local proof infrastructure. -/
private theorem fpUopSource {C F : Type} (op : FpUop) (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.wordOp (.fpUop op)) values source = .val (result, resultState)) :
    ∃ word next, values = [.word64 word] ∧ DataSem.consumeSpace 3 source = some next ∧
      result = .word64 (fpSemFpUopComp op word) ∧
      resultState = DataSem.doStack (.wordOp (.fpUop op)) values
        (DataSem.doLimSafe next (.wordOp (.fpUop op)) values) := by
  cases h : DataSem.consumeSpace 3 source with
  | none =>
    simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, h] at run
  | some next =>
    cases values with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        h, DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
    | cons value rest =>
      cases rest with
      | cons x xs => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          h, DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
      | nil =>
        cases value <;> simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral]

/-- A safe unary FP operation has an encodable header; this supports the HOL assignment proof. -/
private theorem fpUopHeaderOfSafe {width : Nat} [NeZero width] {C F : Type}
    (conf : DataToWord.Config) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (l1 l2 : Nat) (locs : List (Nat × Nat))
    (fpu : FpUop) (values : List DataSem.Value)
    (related : stateRel conf l1 l2 source target none locs)
    (safe : DataSem.limSafe source.limits (.wordOp (.fpUop fpu)) values) :
    ∃ hd, encodeHeader (width := width) conf 3 (if width = 64 then 1 else 2) = some hd := by
  have good := related.2.2.2.2.2.2.1
  have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have mem := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, _⟩ := mem
  have lenPos : 0 < conf.lenSize := by
    have h := heapMem.2.2.2.1
    omega
  have lenBound : conf.lenSize + 7 < width := heapMem.2.2.2.2.1
  have limitEq : source.limits.lengthLimit = conf.lenSize := limits.2.1
  have archEq : source.limits.arch64Bit = decide (width = 64) := limits.2.2.1
  rcases good with h | h <;> subst width
  · have safeLen : 1 < conf.lenSize := by
      simp [DataSem.limSafe, archEq, limitEq] at safe
      exact safe.2
    have countBound : 2 < 2 ^ conf.lenSize := by
      have h : 2 ^ 2 ≤ 2 ^ conf.lenSize := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    refine ⟨makeHeader conf (BitVec.ofNat 32 3) 2, ?_⟩
    simp [encodeHeader, countBound, show 3 < 2 ^ (32 - conf.lenSize - 2) by
      have h : 2 ^ 3 ≤ 2 ^ (32 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega]
  · have countBound : 1 < 2 ^ conf.lenSize := by
      have h : 2 ^ 1 ≤ 2 ^ conf.lenSize := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    refine ⟨makeHeader conf (BitVec.ofNat 64 3) 1, ?_⟩
    simp [encodeHeader, countBound, show 3 < 2 ^ (64 - conf.lenSize - 2) by
      have h : 2 ^ 3 ≤ 2 ^ (64 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega]

/-- Evaluate the 64-bit unary FP instruction prefix; this supports the HOL assignment proof. -/
private theorem fpUopPrefix64 {C F : Type} (conf : Config) (fpu : FpUop)
    (arg : Nat) (target : WordSemStateFiniteExact 64 C F) (addr : BitVec 64) (word : BitVec 64)
    (real : target.wordExp (realAddr conf (adjustVar arg)) = some (.word addr))
    (domain : target.mdomain (addr + wordSemBytesInWord) = true)
    (load : target.memory (addr + wordSemBytesInWord) = .word word) :
    WordSemStateFiniteExact.evaluate (wordListSeq [
      .assign 3 (.load (.op .add [realAddr conf (adjustVar arg), .const wordSemBytesInWord])),
      .inst (.fp (.fpMovFromReg 0 3 3)), .inst (.fp (fpUopInst fpu)),
      .inst (.fp (.fpMovToReg 3 5 1))]) target =
        (none, WordSemStateFiniteExact.setVar 3 (.word (fpSemFpUopComp fpu word))
          (WordSemStateFiniteExact.setFpVar 1 (fpSemFpUopComp fpu word)
            (WordSemStateFiniteExact.setFpVar 0 word (WordSemStateFiniteExact.setVar 3 (.word word) target)))) := by
  cases fpu <;>
    simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
      WordSemStateFiniteExact.inst, WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
      WordSemStateFiniteExact.fixClock, wordOpHOL, wordOp, theWords, real, domain, load,
      fpUopInst, fpSemFpUopComp, HolFiniteMapExact.updateEq, FUPDATE_HOL,
      sptLookup_sptInsert_same]


/-- Evaluate the 32-bit unary FP instruction prefix; this supports the HOL assignment proof. -/
private theorem fpUopPrefix32 {C F : Type} (conf : Config) (fpu : FpUop)
    (arg : Nat) (target : WordSemStateFiniteExact 32 C F) (addr : BitVec 32) (word : BitVec 64)
    (real : target.wordExp (realAddr conf (adjustVar arg)) = some (.word addr))
    (domain1 : target.mdomain (addr + wordSemBytesInWord) = true)
    (domain2 : target.mdomain (addr + (2 : BitVec 32) * wordSemBytesInWord) = true)
    (load1 : target.memory (addr + wordSemBytesInWord) = .word ((word >>> (32 : Nat)).setWidth 32))
    (load2 : target.memory (addr + (2 : BitVec 32) * wordSemBytesInWord) = .word (word.setWidth 32)) :
    WordSemStateFiniteExact.evaluate (wordListSeq [
      .assign 15 (realAddr conf (adjustVar arg)),
      .assign 11 (.load (.op .add [.var 15, .const wordSemBytesInWord])),
      .assign 13 (.load (.op .add [.var 15, .const (2 * wordSemBytesInWord)])),
      .inst (.fp (.fpMovFromReg 0 13 11)), .inst (.fp (fpUopInst fpu)),
      .inst (.fp (.fpMovToReg 5 3 1))]) target =
        (none, WordSemStateFiniteExact.setVar 3 (.word (((fpSemFpUopComp fpu word) >>> (32 : Nat)).setWidth 32))
          (WordSemStateFiniteExact.setVar 5 (.word ((fpSemFpUopComp fpu word).setWidth 32))
            (WordSemStateFiniteExact.setFpVar 1 (fpSemFpUopComp fpu word)
              (WordSemStateFiniteExact.setFpVar 0 word
                (WordSemStateFiniteExact.setVar 13 (.word (word.setWidth 32))
                  (WordSemStateFiniteExact.setVar 11 (.word ((word >>> (32 : Nat)).setWidth 32))
                    (WordSemStateFiniteExact.setVar 15 (.word addr) target))))))) := by
  have combine : (((word >>> (32 : Nat)).setWidth 32 ++ word.setWidth 32).setWidth 64) = word := by simpa using word64HalvesAppend word
  have combineExact : (word >>> (32 : Nat)).setWidth 32 ++ word.setWidth 32 = word := by simpa using combine
  have extractLow (v : BitVec 64) : holWordExtract 31 0 v 32 = v.setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.toNat_setWidth]
  have extractHigh (v : BitVec 64) : holWordExtract 63 32 v 32 = (v >>> (32 : Nat)).setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.toNat_setWidth]
  simp only [BitVec.ofNat_eq_ofNat] at domain2 load2
  cases fpu <;>
    simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
      WordSemStateFiniteExact.inst, WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
      WordSemStateFiniteExact.fixClock, wordOpHOL, wordOp, theWords, real, domain1, domain2, load1, load2,
      fpUopInst, fpSemFpUopComp, HolFiniteMapExact.updateEq, FUPDATE_HOL,
      sptLookup_sptInsert_same, sptLookup_sptInsert_ne, extractLow, extractHigh]
  all_goals rw [combineExact]; simp


/-- Unary floating-point operations satisfy the full data-to-word assignment goal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_FP_uop" 14467
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignFpUop_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F) (target : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ fpu, op = .wordOp (.fpUop fpu)) (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values) (_depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r, WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q,r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace → stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  obtain ⟨fpu, rfl⟩ := opIs
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    obtain ⟨word, next, valuesEq, spaceEq, resultEq, stateEq⟩ := fpUopSource fpu values source resultState result run
    subst values
    subst result
    subst resultState
    have argLen := DataSpace.getVars_length args source.locals [.word64 word] argsEq
    cases args with
    | nil => simp at argLen
    | cons arg rest =>
      cases rest with
      | cons x xs => simp at argLen
      | nil =>
        have nextEq : next = { source with space := source.space - 3 } := by
          unfold DataSem.consumeSpace at spaceEq
          split at spaceEq <;> simp_all
        subst next
        have nextRel : stateRel conf l1 l2
            (DataSem.doStack (.wordOp (.fpUop fpu)) [.word64 word]
              (DataSem.doLimSafe source (.wordOp (.fpUop fpu)) [.word64 word])) target none locs :=
          stateRel_doStack conf l1 l2 _ target locs _ _
            (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
        by_cases hasFp : conf.hasFpOps = true
        · cases header : encodeHeader (width := width) conf 3 (if width = 64 then 1 else 2) with
          | some hd =>
            obtain ⟨words, getWords, lengthEq⟩ :=
              stateRel_getVars conf l1 l2 source target locs [arg] [.word64 word] related argsEq
            cases words with
            | nil => simp at lengthEq
            | cons loc rest =>
              cases rest with
              | cons x xs => simp at lengthEq
              | nil =>
                let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
                  flatStack source.stack target.stack
                let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
                have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
                  target.store target.memory target.mdomain target envs [arg] [.word64 word] [loc] (by
                    refine ⟨?_, argsEq, getWords⟩
                    simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
                have good := related.2.2.2.2.2.2.1
                obtain ⟨index, addr, originalHeader, locEq, realAddrEq, domainHeader, headerWord,
                  bit3, bit4, bit2, domainFirst, payload⟩ :=
                    memoryRel_word64Imp conf target.be (holThe source.tstamps) source.refs source.space
                      target.store target.memory target.mdomain word loc (locals ++ envs)
                      ⟨by simpa [locals, envs, List.append_assoc] using roots, good⟩
                have locRead : WordSemStateFiniteExact.getVar (adjustVar arg) target = some loc := by
                  cases found : WordSemStateFiniteExact.getVar (adjustVar arg) target <;>
                    simp_all [WordSemStateFiniteExact.getVars]
                have pointerRead : WordSemStateFiniteExact.getVar (adjustVar arg) target =
                    some (.word (getAddr conf index (.word 0))) := by simpa [locEq] using locRead
                have realEval := Bignum.getRealAddr_lemma conf (adjustVar arg) target
                  (getAddr conf index (.word 0)) addr
                  ⟨related.2.2.2.2.2.2.2.1, good, pointerRead, realAddrEq⟩
                have spaceEnough : 3 ≤ source.space := by
                  unfold DataSem.consumeSpace at spaceEq
                  split at spaceEq <;> simp_all
                rcases good with width32 | width64
                · subst width
                  simp only [show 32 < 64 by decide, ↓reduceIte] at payload
                  obtain ⟨payloadHigh, domainSecond, payloadLow, decoded, originalHeaderEq⟩ := payload
                  let resultWord := fpSemFpUopComp fpu word
                  let pre := WordSemStateFiniteExact.setVar 3 (.word ((resultWord >>> (32 : Nat)).setWidth 32))
                    (WordSemStateFiniteExact.setVar 5 (.word (resultWord.setWidth 32))
                      (WordSemStateFiniteExact.setFpVar 1 resultWord
                        (WordSemStateFiniteExact.setFpVar 0 word
                          (WordSemStateFiniteExact.setVar 13 (.word (word.setWidth 32))
                            (WordSemStateFiniteExact.setVar 11 (.word ((word >>> (32 : Nat)).setWidth 32))
                              (WordSemStateFiniteExact.setVar 15 (.word addr) target))))))
                  have prefixEval := fpUopPrefix32 conf fpu arg target addr word realEval
                    (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domainFirst)
                    (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domainSecond)
                    (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadHigh)
                    (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadLow)
                  have preHeap : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                      pre.store pre.memory pre.mdomain (joinEnvLocals source.locals pre.locals ++ envs) := by
                    simpa [pre, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar,
                      joinEnvLocals_insertOdd, inter_insertOdd_adjustSet, envs, joinEnvLocals] using
                        related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                  have preLow : pre.getVar 5 = some (.word (resultWord.setWidth 32)) := by
                    simp [pre, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                      sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
                  have preHigh : pre.getVar 3 = some (.word ((resultWord >>> (32 : Nat)).setWidth 32)) := by
                    simp [pre, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                      sptLookup_sptInsert_same]
                  have prePresent : ∀ k, (sptLookup k source.locals).isSome →
                      (sptLookup (adjustVar k) pre.locals).isSome := by
                    intro k present
                    have odd3 : adjustVar k ≠ 3 := by simp [adjustVar]
                    have odd5 : adjustVar k ≠ 5 := by simp [adjustVar]; omega
                    have odd11 : adjustVar k ≠ 11 := by simp [adjustVar]; omega
                    have odd13 : adjustVar k ≠ 13 := by simp [adjustVar]; omega
                    have odd15 : adjustVar k ≠ 15 := by simp [adjustVar]; omega
                    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, presentOld, _⟩ := related
                    simpa [pre, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar,
                      sptLookup_sptInsert_ne _ _ _ _ odd3, sptLookup_sptInsert_ne _ _ _ _ odd5,
                      sptLookup_sptInsert_ne _ _ _ _ odd11, sptLookup_sptInsert_ne _ _ _ _ odd13,
                      sptLookup_sptInsert_ne _ _ _ _ odd15] using presentOld k present
                  have writeRun := evaluateWriteWord64On32 (β := PUnit) conf target.be (holThe source.tstamps)
                    source.space source.refs pre source.locals envs 5 3 dest resultWord hd
                    preHeap preLow preHigh related.2.2.2.2.2.2.2.1 (by decide) (by decide) (by omega) rfl
                    (by simpa using header) prePresent
                  obtain ⟨nf, memory, locals1, unused, writeEval, writeHeap, localsPreserved,
                    destPresent, zeroEq⟩ := writeRun
                  have finalHeap : memoryRel conf target.be (holThe source.tstamps) source.refs
                      (source.space - 3) (target.store.update (.nextFree, nf)) memory target.mdomain
                      (joinEnvLocals (sptInsert dest (.word64 resultWord) source.locals) locals1 ++ envs) := by
                    simpa [pre, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar] using writeHeap
                  let nextSource := DataSem.doStack (.wordOp (.fpUop fpu)) [.word64 word]
                    (DataSem.doLimSafe source (.wordOp (.fpUop fpu)) [.word64 word])
                  have finalRel := stateRelNextFreeResult conf l1 l2 dest (source.space - 3)
                    nextSource target locs (.word64 resultWord) nf memory locals1 pre.fpRegs nextRel
                    (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe] using localsPreserved)
                    destPresent
                    (by simpa [pre, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar,
                      sptLookup_sptInsert_ne] using zeroEq)
                    (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe, envs] using finalHeap)
                  have header32 : encodeHeader (width := 32) conf 3 2 = some hd := by simpa using header
                  have seqRun := evalListAppend [
                    .assign 15 (realAddr conf (adjustVar arg)),
                    .assign 11 (.load (.op .add [.var 15, .const wordSemBytesInWord])),
                    .assign 13 (.load (.op .add [.var 15, .const (2 * wordSemBytesInWord)])),
                    .inst (.fp (.fpMovFromReg 0 13 11)), .inst (.fp (fpUopInst fpu)),
                    .inst (.fp (.fpMovToReg 5 3 1))] (writeWord64On32 conf hd dest 5 3) target pre
                    (by simpa [pre, resultWord] using prefixEval)
                  rw [writeEval] at seqRun
                  refine ⟨none, {pre with store := pre.store.update (.nextFree, nf), memory := memory, locals := locals1}, ?_, ?_, ?_⟩
                  · simpa [compileAssign, arg1, assignFpUop_expansion, hasFp, header32] using seqRun
                  · simp
                  · intro _
                    refine ⟨?_, rfl⟩
                    simpa [nextSource, resultWord, pre, DataSem.doStack, DataSem.doLimSafe,
                      WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar] using finalRel
                · subst width
                  simp only [show ¬ 64 < 64 by decide, ↓reduceIte] at payload
                  obtain ⟨payloadWord, decoded, originalHeaderEq⟩ := payload
                  let resultWord := fpSemFpUopComp fpu word
                  let pre := WordSemStateFiniteExact.setVar 3 (.word resultWord)
                    (WordSemStateFiniteExact.setFpVar 1 resultWord
                      (WordSemStateFiniteExact.setFpVar 0 word
                        (WordSemStateFiniteExact.setVar 3 (.word word) target)))
                  have prefixEval := fpUopPrefix64 conf fpu arg target addr word realEval
                    (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domainFirst)
                    (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadWord)
                  have preHeap : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                      pre.store pre.memory pre.mdomain (joinEnvLocals source.locals pre.locals ++ envs) := by
                    simpa [pre, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar,
                      joinEnvLocals_insertOdd, inter_insertOdd_adjustSet, envs, joinEnvLocals] using
                        related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                  have preRead : pre.getVar 3 = some (.word resultWord) := by
                    simp [pre, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                      sptLookup_sptInsert_same]
                  have prePresent : ∀ k, (sptLookup k source.locals).isSome →
                      (sptLookup (adjustVar k) pre.locals).isSome := by
                    intro k present
                    have odd : adjustVar k ≠ 3 := by simp [adjustVar]
                    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, presentOld, _⟩ := related
                    simpa [pre, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar,
                      sptLookup_sptInsert_ne _ _ _ _ odd] using presentOld k present
                  have writeRun := evaluateWriteWord64 (β := PUnit) conf target.be (holThe source.tstamps)
                    source.space source.refs pre source.locals envs 3 dest resultWord hd
                    preHeap preRead related.2.2.2.2.2.2.2.1 (by decide) (by omega) rfl
                    (by simpa using header) prePresent
                  obtain ⟨nf, memory, locals1, unused, writeEval, writeHeap, localsPreserved,
                    destPresent, zeroEq⟩ := writeRun
                  have smallerHeap : memoryRel conf target.be (holThe source.tstamps) source.refs
                      (source.space - 3) (target.store.update (.nextFree, nf)) memory target.mdomain
                      (joinEnvLocals (sptInsert dest (.word64 resultWord) source.locals) locals1 ++ envs) := by
                    apply memoryRel_lessSpace conf target.be (holThe source.tstamps) source.refs
                      (source.space - 2) (source.space - 3) _ _ _ _
                    refine ⟨?_, by omega⟩
                    simpa [pre, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar] using writeHeap
                  let nextSource := DataSem.doStack (.wordOp (.fpUop fpu)) [.word64 word]
                    (DataSem.doLimSafe source (.wordOp (.fpUop fpu)) [.word64 word])
                  have finalRel := stateRelNextFreeResult conf l1 l2 dest (source.space - 3)
                    nextSource target locs (.word64 resultWord) nf memory locals1 pre.fpRegs nextRel
                    (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe] using localsPreserved)
                    destPresent
                    (by simpa [pre, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar,
                      sptLookup_sptInsert_ne] using zeroEq)
                    (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe, envs] using smallerHeap)
                  have header64 : encodeHeader (width := 64) conf 3 1 = some hd := by simpa using header
                  have seqRun := evalListAppend [
                    .assign 3 (.load (.op .add [realAddr conf (adjustVar arg), .const wordSemBytesInWord])),
                    .inst (.fp (.fpMovFromReg 0 3 3)), .inst (.fp (fpUopInst fpu)),
                    .inst (.fp (.fpMovToReg 3 5 1))] (writeWord64 conf hd dest 3) target pre
                    (by simpa [pre, resultWord] using prefixEval)
                  rw [writeEval] at seqRun
                  refine ⟨none, {pre with store := pre.store.update (.nextFree, nf), memory := memory, locals := locals1}, ?_, ?_, ?_⟩
                  · simpa [compileAssign, arg1, assignFpUop_expansion, hasFp, header64] using seqRun
                  · simp
                  · intro _
                    refine ⟨?_, rfl⟩
                    simpa [nextSource, resultWord, pre, DataSem.doStack, DataSem.doLimSafe,
                      WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar] using finalRel
          | none =>
            obtain ⟨out, outEval, outFfi, targetFfi, outMax⟩ := evaluateGiveUp2 conf l1 l2 source target locs related
            have noSafe : ¬ DataSem.limSafe source.limits (.wordOp (.fpUop fpu)) [.word64 word] := by
              intro safe
              obtain ⟨hd, encoded⟩ := fpUopHeaderOfSafe conf source target l1 l2 locs fpu [.word64 word] related safe
              rw [header] at encoded
              contradiction
            refine ⟨some .notEnoughSpace, out, ?_, ?_, ?_⟩
            · simpa [compileAssign, arg1, assignFpUop_expansion, hasFp, header] using outEval
            · intro _
              refine ⟨outFfi.trans targetFfi.symm, ?_, ?_⟩
              · have targetBound := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                apply BackendProps.optionLe_trans _ _ _ ⟨outMax, ?_⟩
                simpa [DataSem.doStack, DataSem.doLimSafe] using targetBound
              · intro _
                simp [DataSem.doStack, DataSem.doLimSafe, noSafe]
            · simp
        · obtain ⟨out, outEval, outFfi, targetFfi, outMax⟩ := evaluateGiveUp2 conf l1 l2 source target locs related
          have noSafe : ¬ DataSem.limSafe source.limits (.wordOp (.fpUop fpu)) [.word64 word] := by
            have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            simp [DataSem.limSafe, limitsInv] at limits ⊢
            aesop
          refine ⟨some .notEnoughSpace, out, ?_, ?_, ?_⟩
          · simpa [compileAssign, arg1, assignFpUop, hasFp] using outEval
          · intro _
            refine ⟨outFfi.trans targetFfi.symm, ?_, ?_⟩
            · have targetBound := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
              apply BackendProps.optionLe_trans _ _ _ ⟨outMax, ?_⟩
              simpa [DataSem.doStack, DataSem.doLimSafe] using targetBound
            · intro _
              simp [DataSem.doStack, DataSem.doLimSafe, noSafe]
          · simp


end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
