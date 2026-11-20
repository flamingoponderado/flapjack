module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.FpCommon
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.RealAddress
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Space
@[expose] public section

/-! Ternary floating-point assignment correctness for data-to-word compilation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

namespace FpTopAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end FpTopAssignmentWitness

/-- Invert source ternary FP application for the assignment proof; this is local proof infrastructure. -/
private theorem fpTopSource {C F : Type} (op : FpTop) (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.wordOp (.fpTop op)) values source = .val (result, resultState)) :
    ∃ first second third next, values = [.word64 first, .word64 second, .word64 third] ∧
      DataSem.consumeSpace 3 source = some next ∧
      result = .word64 (fpSemFpTopComp op first second third) ∧
      resultState = DataSem.doStack (.wordOp (.fpTop op)) values
        (DataSem.doLimSafe next (.wordOp (.fpTop op)) values) := by
  cases h : DataSem.consumeSpace 3 source with
  | none =>
    simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, h] at run
  | some next =>
    cases values with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        h, DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
    | cons first rest =>
      cases rest with
      | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          h, DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
      | cons second rest =>
        cases rest with
        | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            h, DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
        | cons third rest =>
          cases rest with
          | cons extra xs => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              h, DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
          | nil =>
            cases first <;> cases second <;> cases third <;>
              simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
                DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral]

/-- A safe ternary FP operation has an encodable header; this supports the HOL assignment proof. -/
private theorem fpTopHeaderOfSafe {width : Nat} [NeZero width] {C F : Type}
    (conf : DataToWord.Config) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (l1 l2 : Nat) (locs : List (Nat × Nat))
    (fpt : FpTop) (values : List DataSem.Value)
    (related : stateRel conf l1 l2 source target none locs)
    (safe : DataSem.limSafe source.limits (.wordOp (.fpTop fpt)) values) :
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
      exact safe.2.2
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


/-- Evaluate the 64-bit ternary FP prefix; this supports the HOL assignment proof. -/
private theorem fpTopPrefix64 {C F : Type} (conf : Config) (fpt : FpTop)
    (arg1 arg2 arg3 : Nat) (target : WordSemStateFiniteExact 64 C F)
    (addr1 addr2 addr3 : BitVec 64) (w1 w2 w3 : BitVec 64)
    (real1 : target.wordExp (realAddr conf (adjustVar arg1)) = some (.word addr1))
    (real2 : (WordSemStateFiniteExact.setVar 3 (.word w1) target).wordExp
      (realAddr conf (adjustVar arg2)) = some (.word addr2))
    (real3 : (WordSemStateFiniteExact.setVar 5 (.word w2) (WordSemStateFiniteExact.setVar 3 (.word w1) target)).wordExp
      (realAddr conf (adjustVar arg3)) = some (.word addr3))
    (domain1 : target.mdomain (addr1 + wordSemBytesInWord) = true)
    (domain2 : target.mdomain (addr2 + wordSemBytesInWord) = true)
    (domain3 : target.mdomain (addr3 + wordSemBytesInWord) = true)
    (load1 : target.memory (addr1 + wordSemBytesInWord) = .word w1)
    (load2 : target.memory (addr2 + wordSemBytesInWord) = .word w2)
    (load3 : target.memory (addr3 + wordSemBytesInWord) = .word w3) :
    WordSemStateFiniteExact.evaluate (wordListSeq [
      .assign 3 (.load (.op .add [realAddr conf (adjustVar arg1), .const wordSemBytesInWord])),
      .assign 5 (.load (.op .add [realAddr conf (adjustVar arg2), .const wordSemBytesInWord])),
      .assign 7 (.load (.op .add [realAddr conf (adjustVar arg3), .const wordSemBytesInWord])),
      .inst (.fp (.fpMovFromReg 0 3 3)), .inst (.fp (.fpMovFromReg 1 5 5)),
      .inst (.fp (.fpMovFromReg 2 7 7)), .inst (.fp (fpTopInst fpt)), .inst (.fp (.fpMovToReg 3 5 0))]) target =
        (none, WordSemStateFiniteExact.setVar 3 (.word (fpSemFpTopComp fpt w1 w2 w3))
          (WordSemStateFiniteExact.setFpVar 0 (fpSemFpTopComp fpt w1 w2 w3)
            (WordSemStateFiniteExact.setFpVar 2 w3 (WordSemStateFiniteExact.setFpVar 1 w2
              (WordSemStateFiniteExact.setFpVar 0 w1 (WordSemStateFiniteExact.setVar 7 (.word w3)
                (WordSemStateFiniteExact.setVar 5 (.word w2) (WordSemStateFiniteExact.setVar 3 (.word w1) target)))))))) := by
  simp only [WordSemStateFiniteExact.setVar] at real2 real3
  cases fpt
  simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
      WordSemStateFiniteExact.inst, WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
      WordSemStateFiniteExact.fixClock, wordOpHOL, wordOp, theWords, real1, real2, real3,
      domain1, domain2, domain3, load1, load2, load3, fpTopInst, fpSemFpTopComp,
      HolFiniteMapExact.updateEq, FUPDATE_HOL, sptLookup_sptInsert_same, sptLookup_sptInsert_ne]

/-- Evaluate the 32-bit ternary FP prefix; this supports the HOL assignment proof. -/
private theorem fpTopPrefix32 {C F : Type} (conf : Config) (fpt : FpTop)
    (arg1 arg2 arg3 : Nat) (target : WordSemStateFiniteExact 32 C F)
    (addr1 addr2 addr3 : BitVec 32) (w1 w2 w3 : BitVec 64)
    (real1 : target.wordExp (realAddr conf (adjustVar arg1)) = some (.word addr1))
    (real2 : (WordSemStateFiniteExact.setVar 15 (.word addr1) target).wordExp
      (realAddr conf (adjustVar arg2)) = some (.word addr2))
    (real3 : (WordSemStateFiniteExact.setVar 17 (.word addr2) (WordSemStateFiniteExact.setVar 15 (.word addr1) target)).wordExp
      (realAddr conf (adjustVar arg3)) = some (.word addr3))
    (domain11 : target.mdomain (addr1 + wordSemBytesInWord) = true)
    (domain12 : target.mdomain (addr1 + (2 : BitVec 32) * wordSemBytesInWord) = true)
    (domain21 : target.mdomain (addr2 + wordSemBytesInWord) = true)
    (domain22 : target.mdomain (addr2 + (2 : BitVec 32) * wordSemBytesInWord) = true)
    (domain31 : target.mdomain (addr3 + wordSemBytesInWord) = true)
    (domain32 : target.mdomain (addr3 + (2 : BitVec 32) * wordSemBytesInWord) = true)
    (load11 : target.memory (addr1 + wordSemBytesInWord) = .word ((w1 >>> (32 : Nat)).setWidth 32))
    (load12 : target.memory (addr1 + (2 : BitVec 32) * wordSemBytesInWord) = .word (w1.setWidth 32))
    (load21 : target.memory (addr2 + wordSemBytesInWord) = .word ((w2 >>> (32 : Nat)).setWidth 32))
    (load22 : target.memory (addr2 + (2 : BitVec 32) * wordSemBytesInWord) = .word (w2.setWidth 32))
    (load31 : target.memory (addr3 + wordSemBytesInWord) = .word ((w3 >>> (32 : Nat)).setWidth 32))
    (load32 : target.memory (addr3 + (2 : BitVec 32) * wordSemBytesInWord) = .word (w3.setWidth 32)) :
    WordSemStateFiniteExact.evaluate (wordListSeq [
      .assign 15 (realAddr conf (adjustVar arg1)), .assign 17 (realAddr conf (adjustVar arg2)),
      .assign 19 (realAddr conf (adjustVar arg3)),
      .assign 11 (.load (.op .add [.var 15, .const wordSemBytesInWord])),
      .assign 13 (.load (.op .add [.var 15, .const (2 * wordSemBytesInWord)])),
      .assign 21 (.load (.op .add [.var 17, .const wordSemBytesInWord])),
      .assign 23 (.load (.op .add [.var 17, .const (2 * wordSemBytesInWord)])),
      .assign 31 (.load (.op .add [.var 19, .const wordSemBytesInWord])),
      .assign 33 (.load (.op .add [.var 19, .const (2 * wordSemBytesInWord)])),
      .inst (.fp (.fpMovFromReg 0 13 11)), .inst (.fp (.fpMovFromReg 1 23 21)),
      .inst (.fp (.fpMovFromReg 2 33 31)), .inst (.fp (fpTopInst fpt)), .inst (.fp (.fpMovToReg 5 3 0))]) target =
      (none, WordSemStateFiniteExact.setVar 3 (.word (((fpSemFpTopComp fpt w1 w2 w3) >>> (32 : Nat)).setWidth 32))
        (WordSemStateFiniteExact.setVar 5 (.word ((fpSemFpTopComp fpt w1 w2 w3).setWidth 32))
          (WordSemStateFiniteExact.setFpVar 0 (fpSemFpTopComp fpt w1 w2 w3)
            (WordSemStateFiniteExact.setFpVar 2 w3 (WordSemStateFiniteExact.setFpVar 1 w2 (WordSemStateFiniteExact.setFpVar 0 w1
              (WordSemStateFiniteExact.setVar 33 (.word (w3.setWidth 32))
                (WordSemStateFiniteExact.setVar 31 (.word ((w3 >>> (32 : Nat)).setWidth 32))
                  (WordSemStateFiniteExact.setVar 23 (.word (w2.setWidth 32))
                    (WordSemStateFiniteExact.setVar 21 (.word ((w2 >>> (32 : Nat)).setWidth 32))
                      (WordSemStateFiniteExact.setVar 13 (.word (w1.setWidth 32))
                        (WordSemStateFiniteExact.setVar 11 (.word ((w1 >>> (32 : Nat)).setWidth 32))
                          (WordSemStateFiniteExact.setVar 19 (.word addr3) (WordSemStateFiniteExact.setVar 17 (.word addr2)
                            (WordSemStateFiniteExact.setVar 15 (.word addr1) target))))))))))))))) := by
  have combineExact (v : BitVec 64) : (v >>> (32 : Nat)).setWidth 32 ++ v.setWidth 32 = v := by bv_decide
  have extractLow (v : BitVec 64) : holWordExtract 31 0 v 32 = v.setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.toNat_setWidth]
  have extractHigh (v : BitVec 64) : holWordExtract 63 32 v 32 = (v >>> (32 : Nat)).setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.toNat_setWidth]
  simp only [WordSemStateFiniteExact.setVar] at real2 real3
  simp only [BitVec.ofNat_eq_ofNat] at domain12 domain22 domain32 load12 load22 load32
  cases fpt
  simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
      WordSemStateFiniteExact.inst, WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
      WordSemStateFiniteExact.fixClock, wordOpHOL, wordOp, theWords, real1, real2, real3,
      domain11, domain12, domain21, domain22, domain31, domain32, load11, load12, load21, load22, load31, load32,
      fpTopInst, fpSemFpTopComp, HolFiniteMapExact.updateEq, FUPDATE_HOL,
      sptLookup_sptInsert_same, sptLookup_sptInsert_ne, extractLow, extractHigh]
  all_goals rw [combineExact w1, combineExact w2, combineExact w3]; simp

/-- Ternary floating-point operations satisfy the full data-to-word assignment goal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_FP_top" 14159
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignFpTop_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F) (target : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ fpt, op = .wordOp (.fpTop fpt)) (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values) (_depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r, WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q,r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace → stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  obtain ⟨fpt, rfl⟩ := opIs
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    obtain ⟨first, second, third, next, valuesEq, spaceEq, resultEq, stateEq⟩ := fpTopSource fpt values source resultState result run
    subst values
    subst result
    subst resultState
    have argLen := DataSpace.getVars_length args source.locals [.word64 first, .word64 second, .word64 third] argsEq
    cases args with
    | nil => simp at argLen
    | cons arg1 rest =>
      cases rest with
      | nil => simp at argLen
      | cons arg2 rest =>
        cases rest with
        | nil => simp at argLen
        | cons arg3 rest =>
          cases rest with
          | cons x xs => simp at argLen
          | nil =>
            have nextEq : next = { source with space := source.space - 3 } := by
              unfold DataSem.consumeSpace at spaceEq
              split at spaceEq <;> simp_all
            subst next
            have nextRel : stateRel conf l1 l2
                (DataSem.doStack (.wordOp (.fpTop fpt)) [.word64 first, .word64 second, .word64 third]
                  (DataSem.doLimSafe source (.wordOp (.fpTop fpt)) [.word64 first, .word64 second, .word64 third])) target none locs :=
              stateRel_doStack conf l1 l2 _ target locs _ _
                (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
            by_cases capabilities : conf.hasFpOps = true ∧ conf.hasFpTern = true
            · cases header : encodeHeader (width := width) conf 3 (if width = 64 then 1 else 2) with
              | some hd =>
                obtain ⟨words, getWords, lengthEq⟩ :=
                  stateRel_getVars conf l1 l2 source target locs [arg1, arg2, arg3]
                    [.word64 first, .word64 second, .word64 third] related argsEq
                cases words with
                | nil => simp at lengthEq
                | cons loc1 rest =>
                  cases rest with
                  | nil => simp at lengthEq
                  | cons loc2 rest =>
                    cases rest with
                    | nil => simp at lengthEq
                    | cons loc3 rest =>
                      cases rest with
                      | cons x xs => simp at lengthEq
                      | nil =>
                        let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
                          flatStack source.stack target.stack
                        let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
                        have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
                          target.store target.memory target.mdomain target envs [arg1, arg2, arg3]
                            [.word64 first, .word64 second, .word64 third] [loc1, loc2, loc3] (by
                            refine ⟨?_, argsEq, getWords⟩
                            simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
                        have good := related.2.2.2.2.2.2.1
                        have roots1 : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                            target.store target.memory target.mdomain
                            ((.word64 first, loc1) :: (.word64 second, loc2) :: (.word64 third, loc3) :: locals ++ envs) := by
                          simpa [locals, envs, List.append_assoc] using roots
                        have roots2 := memoryRel_tl conf target.be (holThe source.tstamps) source.refs source.space
                          target.store target.memory target.mdomain (.word64 first, loc1)
                            ((.word64 second, loc2) :: (.word64 third, loc3) :: locals ++ envs) roots1
                        have roots3 := memoryRel_tl conf target.be (holThe source.tstamps) source.refs source.space
                          target.store target.memory target.mdomain (.word64 second, loc2) ((.word64 third, loc3) :: locals ++ envs) roots2
                        obtain ⟨index1, addr1, hd1, locEq1, addrEq1, domHd1, head1,
                          bit31, bit41, bit21, domFirst1, payload1⟩ :=
                            memoryRel_word64Imp conf target.be (holThe source.tstamps) source.refs source.space
                              target.store target.memory target.mdomain first loc1
                                ((.word64 second, loc2) :: (.word64 third, loc3) :: locals ++ envs) ⟨roots1, good⟩
                        obtain ⟨index2, addr2, hd2, locEq2, addrEq2, domHd2, head2,
                          bit32, bit42, bit22, domFirst2, payload2⟩ :=
                            memoryRel_word64Imp conf target.be (holThe source.tstamps) source.refs source.space
                              target.store target.memory target.mdomain second loc2 ((.word64 third, loc3) :: locals ++ envs) ⟨roots2, good⟩
                        obtain ⟨index3, addr3, hd3, locEq3, addrEq3, domHd3, head3,
                          bit33, bit43, bit23, domFirst3, payload3⟩ :=
                            memoryRel_word64Imp conf target.be (holThe source.tstamps) source.refs source.space
                              target.store target.memory target.mdomain third loc3 (locals ++ envs) ⟨roots3, good⟩
                        have allReads : WordSemStateFiniteExact.getVar (adjustVar arg1) target = some loc1 ∧
                            WordSemStateFiniteExact.getVar (adjustVar arg2) target = some loc2 ∧
                            WordSemStateFiniteExact.getVar (adjustVar arg3) target = some loc3 := by
                          cases h1 : WordSemStateFiniteExact.getVar (adjustVar arg1) target <;>
                            cases h2 : WordSemStateFiniteExact.getVar (adjustVar arg2) target <;>
                            cases h3 : WordSemStateFiniteExact.getVar (adjustVar arg3) target <;>
                            simp_all [WordSemStateFiniteExact.getVars]
                        have ptrRead1 : target.getVar (adjustVar arg1) = some (.word (getAddr conf index1 (.word 0))) := by
                          simpa [locEq1] using allReads.1
                        have ptrRead2 : target.getVar (adjustVar arg2) = some (.word (getAddr conf index2 (.word 0))) := by
                          simpa [locEq2] using allReads.2.1
                        have ptrRead3 : target.getVar (adjustVar arg3) = some (.word (getAddr conf index3 (.word 0))) := by
                          simpa [locEq3] using allReads.2.2
                        have realEval1 := Bignum.getRealAddr_lemma conf (adjustVar arg1) target
                          (getAddr conf index1 (.word 0)) addr1 ⟨related.2.2.2.2.2.2.2.1, good, ptrRead1, addrEq1⟩
                        have spaceEnough : 3 ≤ source.space := by
                          unfold DataSem.consumeSpace at spaceEq
                          split at spaceEq <;> simp_all
                        rcases good with width32 | width64
                        · subst width
                          simp only [show 32 < 64 by decide, ↓reduceIte] at payload1 payload2 payload3
                          obtain ⟨payloadHigh1, domSecond1, payloadLow1, decoded1, originalHeaderEq1⟩ := payload1
                          obtain ⟨payloadHigh2, domSecond2, payloadLow2, decoded2, originalHeaderEq2⟩ := payload2
                          obtain ⟨payloadHigh3, domSecond3, payloadLow3, decoded3, originalHeaderEq3⟩ := payload3
                          let resultWord := fpSemFpTopComp fpt first second third
                          let pre := WordSemStateFiniteExact.setVar 3 (.word ((resultWord >>> (32 : Nat)).setWidth 32))
                            (WordSemStateFiniteExact.setVar 5 (.word (resultWord.setWidth 32))
                              (WordSemStateFiniteExact.setFpVar 0 resultWord
                                (WordSemStateFiniteExact.setFpVar 2 third (WordSemStateFiniteExact.setFpVar 1 second (WordSemStateFiniteExact.setFpVar 0 first
                                  (WordSemStateFiniteExact.setVar 33 (.word (third.setWidth 32))
                                    (WordSemStateFiniteExact.setVar 31 (.word ((third >>> (32 : Nat)).setWidth 32))
                                      (WordSemStateFiniteExact.setVar 23 (.word (second.setWidth 32))
                                        (WordSemStateFiniteExact.setVar 21 (.word ((second >>> (32 : Nat)).setWidth 32))
                                          (WordSemStateFiniteExact.setVar 13 (.word (first.setWidth 32))
                                            (WordSemStateFiniteExact.setVar 11 (.word ((first >>> (32 : Nat)).setWidth 32))
                                              (WordSemStateFiniteExact.setVar 19 (.word addr3) (WordSemStateFiniteExact.setVar 17 (.word addr2)
                                                (WordSemStateFiniteExact.setVar 15 (.word addr1) target))))))))))))))
                          have realEval2After : (WordSemStateFiniteExact.setVar 15 (.word addr1) target).wordExp
                              (realAddr conf (adjustVar arg2)) = some (.word addr2) := by
                            apply Bignum.getRealAddr_lemma conf (adjustVar arg2) _ (getAddr conf index2 (.word 0)) addr2
                            refine ⟨related.2.2.2.2.2.2.2.1, by simp [goodDimindex], ?_, ?_⟩
                            · have odd : adjustVar arg2 ≠ 15 := by simp [adjustVar]; omega
                              simpa [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                                sptLookup_sptInsert_ne _ _ _ _ odd] using ptrRead2
                            · simpa [WordSemStateFiniteExact.setVar] using addrEq2
                          have realEval3After : (WordSemStateFiniteExact.setVar 17 (.word addr2)
                              (WordSemStateFiniteExact.setVar 15 (.word addr1) target)).wordExp
                              (realAddr conf (adjustVar arg3)) = some (.word addr3) := by
                            apply Bignum.getRealAddr_lemma conf (adjustVar arg3) _ (getAddr conf index3 (.word 0)) addr3
                            refine ⟨related.2.2.2.2.2.2.2.1, by simp [goodDimindex], ?_, ?_⟩
                            · have odd15 : adjustVar arg3 ≠ 15 := by simp [adjustVar]; omega
                              have odd17 : adjustVar arg3 ≠ 17 := by simp [adjustVar]; omega
                              simpa [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                                sptLookup_sptInsert_ne _ _ _ _ odd15, sptLookup_sptInsert_ne _ _ _ _ odd17] using ptrRead3
                            · simpa [WordSemStateFiniteExact.setVar] using addrEq3
                          have prefixEval := fpTopPrefix32 conf fpt arg1 arg2 arg3 target addr1 addr2 addr3 first second third
                            realEval1 realEval2After realEval3After
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domFirst1)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domSecond1)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domFirst2)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domSecond2)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domFirst3)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domSecond3)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadHigh1)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadLow1)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadHigh2)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadLow2)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadHigh3)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadLow3)
                          have preHeap : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                              pre.store pre.memory pre.mdomain (joinEnvLocals source.locals pre.locals ++ envs) := by
                            simpa [pre, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar,
                              joinEnvLocals_insertOdd, inter_insertOdd_adjustSet, envs, joinEnvLocals] using
                                related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                          have preLow : pre.getVar 5 = some (.word (resultWord.setWidth 32)) := by
                            simp [pre, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                              sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
                          have preHigh : pre.getVar 3 = some (.word ((resultWord >>> (32 : Nat)).setWidth 32)) := by
                            simp [pre, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
                          have prePresent : ∀ k, (sptLookup k source.locals).isSome →
                              (sptLookup (adjustVar k) pre.locals).isSome := by
                            intro k present
                            have odd3 : adjustVar k ≠ 3 := by simp [adjustVar]
                            have odd5 : adjustVar k ≠ 5 := by simp [adjustVar]; omega
                            have odd11 : adjustVar k ≠ 11 := by simp [adjustVar]; omega
                            have odd13 : adjustVar k ≠ 13 := by simp [adjustVar]; omega
                            have odd15 : adjustVar k ≠ 15 := by simp [adjustVar]; omega
                            have odd17 : adjustVar k ≠ 17 := by simp [adjustVar]; omega
                            have odd19 : adjustVar k ≠ 19 := by simp [adjustVar]; omega
                            have odd21 : adjustVar k ≠ 21 := by simp [adjustVar]; omega
                            have odd23 : adjustVar k ≠ 23 := by simp [adjustVar]; omega
                            have odd31 : adjustVar k ≠ 31 := by simp [adjustVar]; omega
                            have odd33 : adjustVar k ≠ 33 := by simp [adjustVar]; omega
                            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, presentOld, _⟩ := related
                            simpa [pre, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar,
                              sptLookup_sptInsert_ne _ _ _ _ odd3, sptLookup_sptInsert_ne _ _ _ _ odd5,
                              sptLookup_sptInsert_ne _ _ _ _ odd11, sptLookup_sptInsert_ne _ _ _ _ odd13,
                              sptLookup_sptInsert_ne _ _ _ _ odd15, sptLookup_sptInsert_ne _ _ _ _ odd17,
                              sptLookup_sptInsert_ne _ _ _ _ odd19, sptLookup_sptInsert_ne _ _ _ _ odd21,
                              sptLookup_sptInsert_ne _ _ _ _ odd23, sptLookup_sptInsert_ne _ _ _ _ odd31,
                              sptLookup_sptInsert_ne _ _ _ _ odd33] using presentOld k present
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
                          let nextSource := DataSem.doStack (.wordOp (.fpTop fpt)) [.word64 first, .word64 second, .word64 third]
                            (DataSem.doLimSafe source (.wordOp (.fpTop fpt)) [.word64 first, .word64 second, .word64 third])
                          have finalRel := stateRelNextFreeResult conf l1 l2 dest (source.space - 3)
                            nextSource target locs (.word64 resultWord) nf memory locals1 pre.fpRegs nextRel
                            (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe] using localsPreserved)
                            destPresent
                            (by simpa [pre, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar,
                              sptLookup_sptInsert_ne] using zeroEq)
                            (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe, envs] using finalHeap)
                          have header32 : encodeHeader (width := 32) conf 3 2 = some hd := by simpa using header
                          have seqRun := evalListAppend [
                            .assign 15 (realAddr conf (adjustVar arg1)), .assign 17 (realAddr conf (adjustVar arg2)),
                            .assign 19 (realAddr conf (adjustVar arg3)),
                            .assign 11 (.load (.op .add [.var 15, .const wordSemBytesInWord])),
                            .assign 13 (.load (.op .add [.var 15, .const (2 * wordSemBytesInWord)])),
                            .assign 21 (.load (.op .add [.var 17, .const wordSemBytesInWord])),
                            .assign 23 (.load (.op .add [.var 17, .const (2 * wordSemBytesInWord)])),
                            .assign 31 (.load (.op .add [.var 19, .const wordSemBytesInWord])),
                            .assign 33 (.load (.op .add [.var 19, .const (2 * wordSemBytesInWord)])),
                            .inst (.fp (.fpMovFromReg 0 13 11)), .inst (.fp (.fpMovFromReg 1 23 21)),
                            .inst (.fp (.fpMovFromReg 2 33 31)), .inst (.fp (fpTopInst fpt)), .inst (.fp (.fpMovToReg 5 3 0))]
                            (writeWord64On32 conf hd dest 5 3) target pre (by simpa [pre, resultWord] using prefixEval)
                          rw [writeEval] at seqRun
                          refine ⟨none, {pre with store := pre.store.update (.nextFree, nf), memory := memory, locals := locals1}, ?_, ?_, ?_⟩
                          · simpa [compileAssign, DataToWord.arg3, assignFpTop_expansion, capabilities.1, capabilities.2, header32] using seqRun
                          · simp
                          · intro _
                            refine ⟨?_, rfl⟩
                            simpa [nextSource, resultWord, pre, DataSem.doStack, DataSem.doLimSafe,
                              WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar] using finalRel
                        · subst width
                          simp only [show ¬ 64 < 64 by decide, ↓reduceIte] at payload1 payload2 payload3
                          obtain ⟨payloadWord1, decoded1, originalHeaderEq1⟩ := payload1
                          obtain ⟨payloadWord2, decoded2, originalHeaderEq2⟩ := payload2
                          obtain ⟨payloadWord3, decoded3, originalHeaderEq3⟩ := payload3
                          let resultWord := fpSemFpTopComp fpt first second third
                          let pre := WordSemStateFiniteExact.setVar 3 (.word resultWord)
                            (WordSemStateFiniteExact.setFpVar 0 resultWord
                              (WordSemStateFiniteExact.setFpVar 2 third (WordSemStateFiniteExact.setFpVar 1 second
                                (WordSemStateFiniteExact.setFpVar 0 first (WordSemStateFiniteExact.setVar 7 (.word third)
                                  (WordSemStateFiniteExact.setVar 5 (.word second) (WordSemStateFiniteExact.setVar 3 (.word first) target)))))))
                          have realEval2After : (WordSemStateFiniteExact.setVar 3 (.word first) target).wordExp
                              (realAddr conf (adjustVar arg2)) = some (.word addr2) := by
                            apply Bignum.getRealAddr_lemma conf (adjustVar arg2) _ (getAddr conf index2 (.word 0)) addr2
                            refine ⟨related.2.2.2.2.2.2.2.1, by simp [goodDimindex], ?_, ?_⟩
                            · have odd : adjustVar arg2 ≠ 3 := by simp [adjustVar]
                              simpa [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                                sptLookup_sptInsert_ne _ _ _ _ odd] using ptrRead2
                            · simpa [WordSemStateFiniteExact.setVar] using addrEq2
                          have realEval3After : (WordSemStateFiniteExact.setVar 5 (.word second)
                              (WordSemStateFiniteExact.setVar 3 (.word first) target)).wordExp
                              (realAddr conf (adjustVar arg3)) = some (.word addr3) := by
                            apply Bignum.getRealAddr_lemma conf (adjustVar arg3) _ (getAddr conf index3 (.word 0)) addr3
                            refine ⟨related.2.2.2.2.2.2.2.1, by simp [goodDimindex], ?_, ?_⟩
                            · have odd3 : adjustVar arg3 ≠ 3 := by simp [adjustVar]
                              have odd5 : adjustVar arg3 ≠ 5 := by simp [adjustVar]; omega
                              simpa [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                                sptLookup_sptInsert_ne _ _ _ _ odd3, sptLookup_sptInsert_ne _ _ _ _ odd5] using ptrRead3
                            · simpa [WordSemStateFiniteExact.setVar] using addrEq3
                          have prefixEval := fpTopPrefix64 conf fpt arg1 arg2 arg3 target addr1 addr2 addr3 first second third
                            realEval1 realEval2After realEval3After
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domFirst1)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domFirst2)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domFirst3)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadWord1)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadWord2)
                            (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadWord3)
                          have preHeap : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                              pre.store pre.memory pre.mdomain (joinEnvLocals source.locals pre.locals ++ envs) := by
                            simpa [pre, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar,
                              joinEnvLocals_insertOdd, inter_insertOdd_adjustSet, envs, joinEnvLocals] using
                                related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                          have preRead : pre.getVar 3 = some (.word resultWord) := by
                            simp [pre, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
                          have prePresent : ∀ k, (sptLookup k source.locals).isSome →
                              (sptLookup (adjustVar k) pre.locals).isSome := by
                            intro k present
                            have odd3 : adjustVar k ≠ 3 := by simp [adjustVar]
                            have odd5 : adjustVar k ≠ 5 := by simp [adjustVar]; omega
                            have odd7 : adjustVar k ≠ 7 := by simp [adjustVar]; omega
                            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, presentOld, _⟩ := related
                            simpa [pre, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar,
                              sptLookup_sptInsert_ne _ _ _ _ odd3, sptLookup_sptInsert_ne _ _ _ _ odd5,
                              sptLookup_sptInsert_ne _ _ _ _ odd7] using presentOld k present
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
                          let nextSource := DataSem.doStack (.wordOp (.fpTop fpt)) [.word64 first, .word64 second, .word64 third]
                            (DataSem.doLimSafe source (.wordOp (.fpTop fpt)) [.word64 first, .word64 second, .word64 third])
                          have finalRel := stateRelNextFreeResult conf l1 l2 dest (source.space - 3)
                            nextSource target locs (.word64 resultWord) nf memory locals1 pre.fpRegs nextRel
                            (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe] using localsPreserved)
                            destPresent
                            (by simpa [pre, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar,
                              sptLookup_sptInsert_ne] using zeroEq)
                            (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe, envs] using smallerHeap)
                          have header64 : encodeHeader (width := 64) conf 3 1 = some hd := by simpa using header
                          have seqRun := evalListAppend [
                            .assign 3 (.load (.op .add [realAddr conf (adjustVar arg1), .const wordSemBytesInWord])),
                            .assign 5 (.load (.op .add [realAddr conf (adjustVar arg2), .const wordSemBytesInWord])),
                            .assign 7 (.load (.op .add [realAddr conf (adjustVar arg3), .const wordSemBytesInWord])),
                            .inst (.fp (.fpMovFromReg 0 3 3)), .inst (.fp (.fpMovFromReg 1 5 5)),
                            .inst (.fp (.fpMovFromReg 2 7 7)), .inst (.fp (fpTopInst fpt)), .inst (.fp (.fpMovToReg 3 5 0))]
                            (writeWord64 conf hd dest 3) target pre (by simpa [pre, resultWord] using prefixEval)
                          rw [writeEval] at seqRun
                          refine ⟨none, {pre with store := pre.store.update (.nextFree, nf), memory := memory, locals := locals1}, ?_, ?_, ?_⟩
                          · simpa [compileAssign, DataToWord.arg3, assignFpTop_expansion, capabilities.1, capabilities.2, header64] using seqRun
                          · simp
                          · intro _
                            refine ⟨?_, rfl⟩
                            simpa [nextSource, resultWord, pre, DataSem.doStack, DataSem.doLimSafe,
                              WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setFpVar] using finalRel
              | none =>
                obtain ⟨out, outEval, outFfi, targetFfi, outMax⟩ := evaluateGiveUp2 conf l1 l2 source target locs related
                have noSafe : ¬ DataSem.limSafe source.limits (.wordOp (.fpTop fpt)) [.word64 first, .word64 second, .word64 third] := by
                  intro safe
                  obtain ⟨hd, encoded⟩ := fpTopHeaderOfSafe conf source target l1 l2 locs fpt [.word64 first, .word64 second, .word64 third] related safe
                  rw [header] at encoded
                  contradiction
                refine ⟨some .notEnoughSpace, out, ?_, ?_, ?_⟩
                · simpa [compileAssign, DataToWord.arg3, assignFpTop_expansion, capabilities.1, capabilities.2, header] using outEval
                · intro _
                  refine ⟨outFfi.trans targetFfi.symm, ?_, ?_⟩
                  · have targetBound := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                    apply BackendProps.optionLe_trans _ _ _ ⟨outMax, ?_⟩
                    simpa [DataSem.doStack, DataSem.doLimSafe] using targetBound
                  · intro _
                    simp [DataSem.doStack, DataSem.doLimSafe, noSafe]
                · simp
            · obtain ⟨out, outEval, outFfi, targetFfi, outMax⟩ := evaluateGiveUp2 conf l1 l2 source target locs related
              have noSafe : ¬ DataSem.limSafe source.limits (.wordOp (.fpTop fpt)) [.word64 first, .word64 second, .word64 third] := by
                have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                simp [DataSem.limSafe, limitsInv] at limits ⊢
                aesop
              refine ⟨some .notEnoughSpace, out, ?_, ?_, ?_⟩
              · have disabled : conf.hasFpOps = false ∨ conf.hasFpTern = false := by
                  cases h1 : conf.hasFpOps <;> cases h2 : conf.hasFpTern <;> simp_all
                simpa [compileAssign, DataToWord.arg3, assignFpTop_expansion, disabled] using outEval
              · intro _
                refine ⟨outFfi.trans targetFfi.symm, ?_, ?_⟩
                · have targetBound := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                  apply BackendProps.optionLe_trans _ _ _ ⟨outMax, ?_⟩
                  simpa [DataSem.doStack, DataSem.doLimSafe] using targetBound
                · intro _
                  simp [DataSem.doStack, DataSem.doLimSafe, noSafe]
              · simp

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
