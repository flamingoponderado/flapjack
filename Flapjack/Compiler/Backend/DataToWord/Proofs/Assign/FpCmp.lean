module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.FpTop
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BoolTest
@[expose] public section

/-! Floating-point comparison prerequisites for data-to-word assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

/-- Every HOL one-bit word is zero or one. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word1_cases"]
theorem word1Cases (w : BitVec 1) : w = 0 ∨ w = 1 := by bv_decide

/-- Comparison symmetry on finite rational values, used by the local HOL theorem. -/
private theorem ratGreaterSwap (a b : Rat) :
    ((if a < b then HolFloatCompare.lt else if a = b then .eq else .gt) == .gt) =
      ((if b < a then HolFloatCompare.lt else if b = a then .eq else .gt) == .lt) ∧
    (match (if a < b then HolFloatCompare.lt else if a = b then .eq else .gt) with
      | .gt | .eq => true | _ => false) =
    (match (if b < a then HolFloatCompare.lt else if b = a then .eq else .gt) with
      | .lt | .eq => true | _ => false) := by
  rcases lt_trichotomy a b with h | h | h
  · have hba : ¬ b < a := not_lt_of_ge (le_of_lt h)
    have hab : a ≠ b := ne_of_lt h
    have hbaEq : b ≠ a := Ne.symm hab
    simp [h, hba, hbaEq]
  · subst b
    simp
  · have hab : ¬ a < b := not_lt_of_ge (le_of_lt h)
    have hne : b ≠ a := ne_of_lt h
    have hne2 : a ≠ b := Ne.symm hne
    simp [h, hab, hne2]

/-- Comparison symmetry for the shared float model; this is proof infrastructure for `fp_greater`. -/
private theorem floatGreaterSwap {t w : Nat} [NeZero t] [NeZero w] (x y : HolFloat t w) :
    holFloatGreaterThan x y = holFloatLessThan y x ∧
      holFloatGreaterEqual x y = holFloatLessEqual y x := by
  have sx := word1Cases x.sign
  have sy := word1Cases y.sign
  rcases sx with sx | sx <;> rcases sy with sy | sy <;>
    cases hx : holFloatValue x <;> cases hy : holFloatValue y <;>
    simp [holFloatGreaterThan, holFloatLessThan, holFloatGreaterEqual, holFloatLessEqual,
      holFloatCompare, hx, hy, sx, sy, ratGreaterSwap]
  all_goals exact (ratGreaterSwap _ _).2

/-- Greater FP comparisons equal less comparisons with the operands reversed. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "fp_greater"
  (reals_as_rational_cuts)]
theorem fpGreater (a b : BitVec 64) :
    holFp64GreaterThan a b = holFp64LessThan b a ∧
      holFp64GreaterEqual a b = holFp64LessEqual b a := by
  simpa [holFp64GreaterThan, holFp64LessThan, holFp64GreaterEqual, holFp64LessEqual] using
    floatGreaterSwap (holFp64ToFloat a) (holFp64ToFloat b)

namespace FpCmpAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end FpCmpAssignmentWitness

private theorem fpCmpSource {C F : Type} (op : FpCmp) (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.wordOp (.fpCmp op)) values source = .val (result, resultState)) :
    ∃ left right, values = [.word64 left, .word64 right] ∧
      result = DataSem.boolValue (fpSemFpCmpComp op left right) ∧
      resultState = DataSem.doStack (.wordOp (.fpCmp op)) values
        (DataSem.doLimSafe source (.wordOp (.fpCmp op)) values) := by
  cases values with
  | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
  | cons first rest =>
    cases rest with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
    | cons second rest =>
      cases rest with
      | cons extra xs => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
      | nil =>
        cases first <;> cases second <;>
          simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral]


private theorem fpCmpPrefix64 {C F : Type} (conf : Config) (cmp : FpCmp)
    (arg1 arg2 dest : Nat) (target : WordSemStateFiniteExact 64 C F)
    (addr1 addr2 : BitVec 64) (w1 w2 : BitVec 64)
    (real1 : target.wordExp (realAddr conf (adjustVar arg1)) = some (.word addr1))
    (real2 : (WordSemStateFiniteExact.setVar 3 (.word w1) target).wordExp
      (realAddr conf (adjustVar arg2)) = some (.word addr2))
    (domain1 : target.mdomain (addr1 + wordSemBytesInWord) = true)
    (domain2 : target.mdomain (addr2 + wordSemBytesInWord) = true)
    (load1 : target.memory (addr1 + wordSemBytesInWord) = .word w1)
    (load2 : target.memory (addr2 + wordSemBytesInWord) = .word w2) :
    WordSemStateFiniteExact.evaluate (wordListSeq [
      .assign 3 (.load (.op .add [realAddr conf (adjustVar arg1), .const wordSemBytesInWord])),
      .assign 5 (.load (.op .add [realAddr conf (adjustVar arg2), .const wordSemBytesInWord])),
      .inst (.fp (.fpMovFromReg 0 3 3)), .inst (.fp (.fpMovFromReg 1 5 5)),
      .inst (.fp (fpCmpInst cmp)),
      .assign (adjustVar dest) (.op .add [shiftVar .lsl 3 4, .const 2])]) target =
        (none, WordSemStateFiniteExact.setVar (adjustVar dest)
          (.word (if fpSemFpCmpComp cmp w1 w2 then 18 else 2))
          (WordSemStateFiniteExact.setVar 3 (.word (if fpSemFpCmpComp cmp w1 w2 then 1 else 0))
            (WordSemStateFiniteExact.setFpVar 1 w2 (WordSemStateFiniteExact.setFpVar 0 w1
              (WordSemStateFiniteExact.setVar 5 (.word w2) (WordSemStateFiniteExact.setVar 3 (.word w1) target)))))) := by
  simp only [WordSemStateFiniteExact.setVar] at real2
  cases cmp <;>
    simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
      WordSemStateFiniteExact.inst, WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
      WordSemStateFiniteExact.fixClock, wordOpHOL, wordOp, theWords, real1, real2, domain1, domain2, load1, load2,
      fpCmpInst, fpSemFpCmpComp, shiftVar, shiftN, wordShiftHOL, fpGreater, HolFiniteMapExact.updateEq, FUPDATE_HOL,
      sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
  all_goals split <;> simp_all


private theorem fpCmpPrefix32 {C F : Type} (conf : Config) (cmp : FpCmp)
    (arg1 arg2 dest : Nat) (target : WordSemStateFiniteExact 32 C F)
    (addr1 addr2 : BitVec 32) (w1 w2 : BitVec 64)
    (real1 : target.wordExp (realAddr conf (adjustVar arg1)) = some (.word addr1))
    (real2 : (WordSemStateFiniteExact.setVar 15 (.word addr1) target).wordExp
      (realAddr conf (adjustVar arg2)) = some (.word addr2))
    (domain11 : target.mdomain (addr1 + wordSemBytesInWord) = true)
    (domain12 : target.mdomain (addr1 + (2 : BitVec 32) * wordSemBytesInWord) = true)
    (domain21 : target.mdomain (addr2 + wordSemBytesInWord) = true)
    (domain22 : target.mdomain (addr2 + (2 : BitVec 32) * wordSemBytesInWord) = true)
    (load11 : target.memory (addr1 + wordSemBytesInWord) = .word ((w1 >>> (32 : Nat)).setWidth 32))
    (load12 : target.memory (addr1 + (2 : BitVec 32) * wordSemBytesInWord) = .word (w1.setWidth 32))
    (load21 : target.memory (addr2 + wordSemBytesInWord) = .word ((w2 >>> (32 : Nat)).setWidth 32))
    (load22 : target.memory (addr2 + (2 : BitVec 32) * wordSemBytesInWord) = .word (w2.setWidth 32)) :
    WordSemStateFiniteExact.evaluate (wordListSeq [
      .assign 15 (realAddr conf (adjustVar arg1)), .assign 17 (realAddr conf (adjustVar arg2)),
      .assign 11 (.load (.op .add [.var 15, .const wordSemBytesInWord])),
      .assign 13 (.load (.op .add [.var 15, .const (2 * wordSemBytesInWord)])),
      .assign 21 (.load (.op .add [.var 17, .const wordSemBytesInWord])),
      .assign 23 (.load (.op .add [.var 17, .const (2 * wordSemBytesInWord)])),
      .inst (.fp (.fpMovFromReg 0 13 11)), .inst (.fp (.fpMovFromReg 1 23 21)),
      .inst (.fp (fpCmpInst cmp)),
      .assign (adjustVar dest) (.op .add [shiftVar .lsl 3 4, .const 2])]) target =
      (none, WordSemStateFiniteExact.setVar (adjustVar dest)
        (.word (if fpSemFpCmpComp cmp w1 w2 then 18 else 2))
        (WordSemStateFiniteExact.setVar 3 (.word (if fpSemFpCmpComp cmp w1 w2 then 1 else 0))
          (WordSemStateFiniteExact.setFpVar 1 w2 (WordSemStateFiniteExact.setFpVar 0 w1
            (WordSemStateFiniteExact.setVar 23 (.word (w2.setWidth 32))
              (WordSemStateFiniteExact.setVar 21 (.word ((w2 >>> (32 : Nat)).setWidth 32))
                (WordSemStateFiniteExact.setVar 13 (.word (w1.setWidth 32))
                  (WordSemStateFiniteExact.setVar 11 (.word ((w1 >>> (32 : Nat)).setWidth 32))
                    (WordSemStateFiniteExact.setVar 17 (.word addr2)
                      (WordSemStateFiniteExact.setVar 15 (.word addr1) target)))))))))) := by
  have combineExact (v : BitVec 64) : (v >>> (32 : Nat)).setWidth 32 ++ v.setWidth 32 = v := by bv_decide
  simp only [WordSemStateFiniteExact.setVar] at real2
  simp only [BitVec.ofNat_eq_ofNat] at domain12 domain22 load12 load22
  cases cmp <;>
    simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
      WordSemStateFiniteExact.inst, WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
      WordSemStateFiniteExact.fixClock, wordOpHOL, wordOp, theWords, real1, real2,
      domain11, domain12, domain21, domain22, load11, load12, load21, load22,
      fpCmpInst, fpSemFpCmpComp, shiftVar, shiftN, wordShiftHOL, fpGreater, HolFiniteMapExact.updateEq, FUPDATE_HOL,
      sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
  all_goals rw [combineExact w1, combineExact w2]; simp
  all_goals split <;> simp_all


private theorem stateRel_setScratch {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (key : Nat) (value : WordLocW width) (odd : key % 2 = 1)
    (related : stateRel conf l1 l2 source target none locs) :
    stateRel conf l1 l2 source (target.setVar key value) none locs := by
  simpa [WordSemStateFiniteExact.setVar] using
    (stateRel_insertOdd conf l1 l2 source target none locs key value odd).mpr related

private theorem stateRel_setFpScratch {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (key : Nat) (value : BitVec 64)
    (related : stateRel conf l1 l2 source target none locs) :
    stateRel conf l1 l2 source (target.setFpVar key value) none locs := by
  exact stateRel_withFpRegs conf l1 l2 source target none locs _ related

-- Boolean results use the existing memory relation without allocating.
private theorem stateRel_insertBool {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (dest : Nat) (answer : Bool) (related : stateRel conf l1 l2 source target none locs) :
    stateRel conf l1 l2 (DataSem.setVar dest (DataSem.boolValue answer) source)
      (target.setVar (adjustVar dest) (.word (if answer then 18 else 2))) none locs := by
  apply stateRel_insertRoot conf l1 l2 source target locs dest _ _ related
  apply memoryRel_bool conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain _ _ _
  refine ⟨related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, related.2.2.2.2.2.2.1, ?_, ?_⟩
  · intro h; simp [h]
  · intro h; simp [h]

/-- Floating-point comparison satisfies the complete HOL assignment simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_FP_cmp" 14057
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignFpCmp_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F) (target : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ cmp, op = .wordOp (.fpCmp cmp)) (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values) (_depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r, WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q,r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace → stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  obtain ⟨cmp, rfl⟩ := opIs
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    obtain ⟨left, right, valuesEq, resultEq, stateEq⟩ := fpCmpSource cmp values source resultState result run
    subst values
    subst result
    subst resultState
    have argLen := DataSpace.getVars_length args source.locals [.word64 left, .word64 right] argsEq
    cases args with
    | nil => simp at argLen
    | cons arg1 rest =>
      cases rest with
      | nil => simp at argLen
      | cons arg2 rest =>
        cases rest with
        | cons x xs => simp at argLen
        | nil =>
          have nextRel : stateRel conf l1 l2
              (DataSem.doStack (.wordOp (.fpCmp cmp)) [.word64 left, .word64 right]
                (DataSem.doLimSafe source (.wordOp (.fpCmp cmp)) [.word64 left, .word64 right])) target none locs :=
            stateRel_doStack conf l1 l2 _ target locs _ _
              (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
          by_cases hasFp : conf.hasFpOps = true
          ·
            obtain ⟨words, getWords, lengthEq⟩ :=
              stateRel_getVars conf l1 l2 source target locs [arg1, arg2] [.word64 left, .word64 right] related argsEq
            cases words with
            | nil => simp at lengthEq
            | cons loc1 rest =>
              cases rest with
              | nil => simp at lengthEq
              | cons loc2 rest =>
                cases rest with
                | cons x xs => simp at lengthEq
                | nil =>
                  let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
                    flatStack source.stack target.stack
                  let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
                  have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
                    target.store target.memory target.mdomain target envs [arg1, arg2] [.word64 left, .word64 right] [loc1, loc2] (by
                      refine ⟨?_, argsEq, getWords⟩
                      simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
                  have good := related.2.2.2.2.2.2.1
                  have roots1 : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                      target.store target.memory target.mdomain ((.word64 left, loc1) :: (.word64 right, loc2) :: locals ++ envs) := by
                    simpa [locals, envs, List.append_assoc] using roots
                  have roots2 := memoryRel_tl conf target.be (holThe source.tstamps) source.refs source.space
                    target.store target.memory target.mdomain (.word64 left, loc1) ((.word64 right, loc2) :: locals ++ envs) roots1
                  obtain ⟨index1, addr1, hd1, locEq1, addrEq1, domHd1, head1,
                    bit31, bit41, bit21, domFirst1, payload1⟩ :=
                      memoryRel_word64Imp conf target.be (holThe source.tstamps) source.refs source.space
                        target.store target.memory target.mdomain left loc1 ((.word64 right, loc2) :: locals ++ envs) ⟨roots1, good⟩
                  obtain ⟨index2, addr2, hd2, locEq2, addrEq2, domHd2, head2,
                    bit32, bit42, bit22, domFirst2, payload2⟩ :=
                      memoryRel_word64Imp conf target.be (holThe source.tstamps) source.refs source.space
                        target.store target.memory target.mdomain right loc2 (locals ++ envs) ⟨roots2, good⟩
                  have bothReads : WordSemStateFiniteExact.getVar (adjustVar arg1) target = some loc1 ∧
                      WordSemStateFiniteExact.getVar (adjustVar arg2) target = some loc2 := by
                    cases h1 : WordSemStateFiniteExact.getVar (adjustVar arg1) target <;>
                      cases h2 : WordSemStateFiniteExact.getVar (adjustVar arg2) target <;>
                      simp_all [WordSemStateFiniteExact.getVars]
                  have ptrRead1 : target.getVar (adjustVar arg1) = some (.word (getAddr conf index1 (.word 0))) := by
                    simpa [locEq1] using bothReads.1
                  have ptrRead2 : target.getVar (adjustVar arg2) = some (.word (getAddr conf index2 (.word 0))) := by
                    simpa [locEq2] using bothReads.2
                  have realEval1 := Bignum.getRealAddr_lemma conf (adjustVar arg1) target
                    (getAddr conf index1 (.word 0)) addr1 ⟨related.2.2.2.2.2.2.2.1, good, ptrRead1, addrEq1⟩
                  have realEval2 := Bignum.getRealAddr_lemma conf (adjustVar arg2) target
                    (getAddr conf index2 (.word 0)) addr2 ⟨related.2.2.2.2.2.2.2.1, good, ptrRead2, addrEq2⟩
                  rcases good with width32 | width64
                  · subst width
                    simp only [show 32 < 64 by decide, ↓reduceIte] at payload1 payload2
                    obtain ⟨payloadHigh1, domSecond1, payloadLow1, decoded1, originalHeaderEq1⟩ := payload1
                    obtain ⟨payloadHigh2, domSecond2, payloadLow2, decoded2, originalHeaderEq2⟩ := payload2
                    let answer := fpSemFpCmpComp cmp left right
                    let pre := WordSemStateFiniteExact.setVar 3 (.word (if answer then 1 else 0))
                      (WordSemStateFiniteExact.setFpVar 1 right (WordSemStateFiniteExact.setFpVar 0 left
                        (WordSemStateFiniteExact.setVar 23 (.word (right.setWidth 32))
                          (WordSemStateFiniteExact.setVar 21 (.word ((right >>> (32 : Nat)).setWidth 32))
                            (WordSemStateFiniteExact.setVar 13 (.word (left.setWidth 32))
                              (WordSemStateFiniteExact.setVar 11 (.word ((left >>> (32 : Nat)).setWidth 32))
                                (WordSemStateFiniteExact.setVar 17 (.word addr2)
                                  (WordSemStateFiniteExact.setVar 15 (.word addr1) target))))))))
                    have realEval2After : (WordSemStateFiniteExact.setVar 15 (.word addr1) target).wordExp
                        (realAddr conf (adjustVar arg2)) = some (.word addr2) := by
                      apply Bignum.getRealAddr_lemma conf (adjustVar arg2) _ (getAddr conf index2 (.word 0)) addr2
                      refine ⟨related.2.2.2.2.2.2.2.1, by simp [goodDimindex], ?_, ?_⟩
                      · have odd : adjustVar arg2 ≠ 15 := by simp [adjustVar]; omega
                        simpa [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          sptLookup_sptInsert_ne _ _ _ _ odd] using ptrRead2
                      · simpa [WordSemStateFiniteExact.setVar] using addrEq2
                    have prefixEval := fpCmpPrefix32 conf cmp arg1 arg2 dest target addr1 addr2 left right realEval1 realEval2After
                      (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domFirst1)
                      (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domSecond1)
                      (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domFirst2)
                      (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domSecond2)
                      (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadHigh1)
                      (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadLow1)
                      (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadHigh2)
                      (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadLow2)
                    have preRel : stateRel conf l1 l2
                        (DataSem.doStack (.wordOp (.fpCmp cmp)) [.word64 left, .word64 right]
                          (DataSem.doLimSafe source (.wordOp (.fpCmp cmp)) [.word64 left, .word64 right])) pre none locs := by
                      dsimp [pre]
                      apply stateRel_setScratch _ _ _ _ _ _ _ _ (by decide)
                      apply stateRel_setFpScratch
                      apply stateRel_setFpScratch
                      apply stateRel_setScratch _ _ _ _ _ _ _ _ (by decide)
                      apply stateRel_setScratch _ _ _ _ _ _ _ _ (by decide)
                      apply stateRel_setScratch _ _ _ _ _ _ _ _ (by decide)
                      apply stateRel_setScratch _ _ _ _ _ _ _ _ (by decide)
                      apply stateRel_setScratch _ _ _ _ _ _ _ _ (by decide)
                      apply stateRel_setScratch _ _ _ _ _ _ _ _ (by decide)
                      exact nextRel
                    have finalRel := stateRel_insertBool conf l1 l2 _ pre locs dest answer preRel
                    refine ⟨none, pre.setVar (adjustVar dest) (.word (if answer then 18 else 2)), ?_, by simp, ?_⟩
                    · simpa [compileAssign, DataToWord.arg2, assignFpCmp, hasFp, pre, answer] using prefixEval
                    · intro _
                      exact ⟨finalRel, rfl⟩
                  · subst width
                    simp only [show ¬ 64 < 64 by decide, ↓reduceIte] at payload1 payload2
                    let answer := fpSemFpCmpComp cmp left right
                    let pre := WordSemStateFiniteExact.setVar 3 (.word (if answer then 1 else 0))
                      (WordSemStateFiniteExact.setFpVar 1 right (WordSemStateFiniteExact.setFpVar 0 left
                        (WordSemStateFiniteExact.setVar 5 (.word right) (WordSemStateFiniteExact.setVar 3 (.word left) target))))
                    have realEval2After : (WordSemStateFiniteExact.setVar 3 (.word left) target).wordExp
                        (realAddr conf (adjustVar arg2)) = some (.word addr2) := by
                      apply Bignum.getRealAddr_lemma conf (adjustVar arg2) _ (getAddr conf index2 (.word 0)) addr2
                      refine ⟨related.2.2.2.2.2.2.2.1, by simp [goodDimindex], ?_, ?_⟩
                      · have odd : adjustVar arg2 ≠ 3 := by simp [adjustVar]
                        simpa [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          sptLookup_sptInsert_ne _ _ _ _ odd] using ptrRead2
                      · simpa [WordSemStateFiniteExact.setVar] using addrEq2
                    have prefixEval := fpCmpPrefix64 conf cmp arg1 arg2 dest target addr1 addr2 left right realEval1 realEval2After
                      (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domFirst1)
                      (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domFirst2)
                      (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payload1.1)
                      (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payload2.1)
                    have preRel : stateRel conf l1 l2
                        (DataSem.doStack (.wordOp (.fpCmp cmp)) [.word64 left, .word64 right]
                          (DataSem.doLimSafe source (.wordOp (.fpCmp cmp)) [.word64 left, .word64 right])) pre none locs := by
                      dsimp [pre]
                      apply stateRel_setScratch _ _ _ _ _ _ _ _ (by decide)
                      apply stateRel_setFpScratch
                      apply stateRel_setFpScratch
                      apply stateRel_setScratch _ _ _ _ _ _ _ _ (by decide)
                      apply stateRel_setScratch _ _ _ _ _ _ _ _ (by decide)
                      exact nextRel
                    have finalRel := stateRel_insertBool conf l1 l2 _ pre locs dest answer preRel
                    refine ⟨none, pre.setVar (adjustVar dest) (.word (if answer then 18 else 2)), ?_, by simp, ?_⟩
                    · simpa [compileAssign, DataToWord.arg2, assignFpCmp, hasFp, pre, answer] using prefixEval
                    · intro _
                      exact ⟨finalRel, rfl⟩
          · obtain ⟨out, outEval, outFfi, targetFfi, outMax⟩ := evaluateGiveUp2 conf l1 l2 source target locs related
            have noSafe : ¬ DataSem.limSafe source.limits (.wordOp (.fpCmp cmp)) [.word64 left, .word64 right] := by
              have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
              simp [DataSem.limSafe, limitsInv] at limits ⊢
              aesop
            refine ⟨some .notEnoughSpace, out, ?_, ?_, ?_⟩
            · simpa [compileAssign, DataToWord.arg2, assignFpCmp, hasFp] using outEval
            · intro _
              refine ⟨outFfi.trans targetFfi.symm, ?_, ?_⟩
              · have targetBound := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                apply BackendProps.optionLe_trans _ _ _ ⟨outMax, ?_⟩
                simpa [DataSem.doStack, DataSem.doLimSafe] using targetBound
              · intro _
                simp [DataSem.doStack, DataSem.doLimSafe, noSafe]
            · simp

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
