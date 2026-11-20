module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BoolNot
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Offset
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.RealAddress
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MemoryRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutOdd
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateInsert
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteArrayImp
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Number

@[expose] public section

/-! Byte dereference in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

namespace DerefByteAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end DerefByteAssignmentWitness

/-- Decode a nonnegative tagged index in the dereference case. This factors an
intermediate step of the HOL assignment proof. -/
private theorem derefByteIndexShift {width : Nat} [NeZero width] (i : Int)
    (good : goodDimindex width) (small : smallInt width i) (nonneg : 0 ≤ i) :
    (smallnum (width := width) i >>> 2) = BitVec.ofNat width i.toNat := by
  rcases good with hw | hw <;> subst width <;>
    simp [smallInt] at small <;>
    apply BitVec.eq_of_toNat_eq <;>
    simp [smallnum, Int.not_lt.mpr nonneg, BitVec.toNat_ushiftRight] <;>
    omega

/-- Extract the successful byte read used in the HOL assignment proof. -/
private theorem derefByteSourceRun {C F : Type} (cut resultState : DataSem.State C F)
    (values : List DataSem.Value) (result : DataSem.Value)
    (run : DataSem.doApp (.memOp .derefByte) values cut = .val (result, resultState)) :
    ∃ bit ptr index flag bytes, ∃ h : index.toNat < bytes.length,
      values = [.refPtr bit ptr, .number index] ∧ 0 ≤ index ∧
      sptLookup ptr cut.refs = some (.byteArray flag bytes) ∧
      result = .number bytes[index.toNat].toNat ∧
      resultState = DataSem.doStack (.memOp .derefByte) values
        (DataSem.doLimSafe cut (.memOp .derefByte) values) := by
  cases values with
  | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.doAppAux, DataSem.applyNonFfi] at run
  | cons v vs =>
    cases vs with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi] at run
    | cons w ws =>
      cases ws with
      | cons x xs => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi] at run
      | nil =>
        cases v <;> cases w <;>
          simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi]
        rename_i bit ptr index
        have refsEq : (DataSem.doStack (.memOp .derefByte)
            [.refPtr bit ptr, .number index]
            (DataSem.doLimSafe cut (.memOp .derefByte) [.refPtr bit ptr, .number index])).refs = cut.refs := rfl
        rw [refsEq] at run
        cases found : sptLookup ptr cut.refs with
        | none => simp [found] at run
        | some ref =>
          cases ref with
          | byteArray flag bytes =>
            by_cases negative : index < 0
            · simp [found, negative] at run
            · by_cases bound : index.toNat < bytes.length
              · simp [found, negative, bound] at run
                obtain ⟨rfl, rfl⟩ := run
                cases flag <;> simp [Int.not_lt.mp negative] <;> omega
              · simp [found, negative, bound] at run
          | _ => simp [found] at run

/-- Byte dereference satisfies the original data-to-word assignment goal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_DerefByte"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignDerefByte_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .memOp .derefByte)
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
  subst op
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    obtain ⟨bit, ptr, index, flag, bytes, bound, valuesEq, nonneg, found, resultEq, stateEq⟩ :=
      derefByteSourceRun source resultState values result run
    subst values
    subst result
    subst resultState
    have argLen : args.length = 2 := by
      have h := DataSpace.getVars_length args source.locals [.refPtr bit ptr, .number index] argsEq
      simpa using h.symm
    cases args with
    | nil => simp at argLen
    | cons a args =>
      cases args with
      | nil => simp at argLen
      | cons b args =>
        cases args with
        | cons c rest => simp at argLen
        | nil =>
          obtain ⟨words, getWords, lengthEq⟩ :=
            stateRel_getVars conf l1 l2 source target locs [a,b] [.refPtr bit ptr, .number index] related argsEq
          cases words with
          | nil => simp at lengthEq
          | cons word1 words =>
            cases words with
            | nil => simp at lengthEq
            | cons word2 words =>
              cases words with
              | cons word3 rest => simp at lengthEq
              | nil =>
                let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
                  flatStack source.stack target.stack
                have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
                  target.store target.memory target.mdomain target envs [a,b]
                  [.refPtr bit ptr, .number index] [word1,word2] (by
                    refine ⟨?_, argsEq, getWords⟩
                    simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
                have good := related.2.2.2.2.2.2.1
                let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
                obtain ⟨w, address, header, _, wordEq, low, headerEq, _, _, _, _, real,
                  _, _, reads, _, sizeBound⟩ :=
                  memoryRel_byteArrayImp (β := Unit) conf target.be (holThe source.tstamps) source.refs
                    source.space target.store target.memory target.mdomain bit flag ptr bytes word1
                    ((.number index, word2) :: locals ++ envs) ⟨by simpa [locals] using roots, found, good⟩
                have small : smallInt width index := by
                  rcases good with hw | hw <;> subst width <;>
                    simp [smallInt] at sizeBound ⊢ <;> omega
                have tail := memoryRel_tail conf target.be (holThe source.tstamps) source.refs source.space
                  target.store target.memory target.mdomain (.refPtr bit ptr, word1)
                  ((.number index, word2) :: locals ++ envs) (by simpa [locals] using roots)
                have indexEq := memoryRel_numberImp conf target.be (holThe source.tstamps) source.refs
                  source.space target.store target.memory target.mdomain index word2 (locals ++ envs)
                  ⟨good, small, tail⟩
                subst word1
                subst word2
                have operands : WordSemStateFiniteExact.getVar (adjustVar a) target = some (.word w) ∧
                    WordSemStateFiniteExact.getVar (adjustVar b) target = some (.word (smallnum index)) := by
                  cases h1 : WordSemStateFiniteExact.getVar (adjustVar a) target <;>
                    cases h2 : WordSemStateFiniteExact.getVar (adjustVar b) target <;>
                    simp_all [WordSemStateFiniteExact.getVars]
                have realExp := Bignum.getRealAddr_lemma conf (adjustVar a) target w address
                  ⟨related.2.2.2.2.2.2.2.1, good, operands.1, real⟩
                have offsetExp := getRealByteOffset_lemma (adjustVar b) target (smallnum index)
                  ⟨operands.2, good⟩
                have indexShift := derefByteIndexShift index good small nonneg
                rw [indexShift] at offsetExp
                let ad := address + StackRemove.bytesInWord width + BitVec.ofNat width index.toNat
                have addressExp : WordSemStateFiniteExact.wordExp target
                    (.op .add [realAddr conf (adjustVar a), realByteOffset (adjustVar b)]) =
                    some (.word ad) := by
                  simp [WordSemStateFiniteExact.wordExp, realExp, offsetExp, theWords, wordOpHOL,
                    wordOp, ad, StackRemove.bytesInWord, wordSemBytesInWord, BitVec.add_assoc]
                have read := reads index.toNat bound
                let s1 := WordSemStateFiniteExact.setVar 1 (.word ad) target
                let s3 := WordSemStateFiniteExact.setVar 3 (.word (bytes[index.toNat].setWidth width)) s1
                let final := WordSemStateFiniteExact.setVar (adjustVar dest)
                  (.word ((bytes[index.toNat].setWidth width) <<< 2)) s3
                have eval : WordSemStateFiniteExact.evaluate
                    (compileAssign conf n l dest (.memOp .derefByte) [a,b] none).1 target =
                    (none, final) := by
                  simp [compileAssign, arg2, assignDerefByte, wordListSeq,
                    WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
                    WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.fixClock,
                    WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                    sptLookup_sptInsert_same, shiftN, theWords, wordOpHOL, wordOp, wordShiftHOL,
                    addressExp, read, ad, s1, s3, final]
                  rcases good with hw | hw <;> subst width <;> simp
                let next := DataSem.doStack (.memOp .derefByte) [.refPtr bit ptr, .number index]
                  (DataSem.doLimSafe source (.memOp .derefByte) [.refPtr bit ptr, .number index])
                have nextRel : stateRel conf l1 l2 next target none locs :=
                  stateRel_doStack conf l1 l2 _ target locs _ _
                    (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
                have s1Rel : stateRel conf l1 l2 next s1 none locs := by
                  simpa [s1, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using nextRel
                have s3Rel : stateRel conf l1 l2 next s3 none locs := by
                  simpa [s3, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using s1Rel
                have smallByte : BackendCommon.smallEnoughInt (Int.ofNat bytes[index.toNat].toNat) := by
                  have byteBound := bytes[index.toNat].isLt
                  simp [BackendCommon.smallEnoughInt]
                  omega
                have outputEq : (bytes[index.toNat].setWidth width <<< 2) =
                    smallnum (Int.ofNat bytes[index.toNat].toNat) := by
                  have nonnegativeByte : ¬ (Int.ofNat bytes[index.toNat].toNat < 0) := by
                    exact Int.not_lt.mpr (Int.natCast_nonneg _)
                  rw [smallnum, if_neg nonnegativeByte]
                  rcases good with hw | hw <;> subst width <;>
                    apply BitVec.eq_of_toNat_eq <;>
                    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Int.toNat_mul] <;>
                    have byteBound := bytes[index.toNat].isLt <;> omega
                have finalRel : stateRel conf l1 l2
                    (DataSem.setVar dest (.number bytes[index.toNat].toNat) next) final none locs := by
                  dsimp only [final]
                  rw [outputEq]
                  exact
                    stateRel_setConst conf l1 l2 next s3 locs dest (Int.ofNat bytes[index.toNat].toNat) s3Rel smallByte
                refine ⟨none, final, eval, ?_, ?_⟩
                · simp
                · intro _
                  exact ⟨finalRel, rfl⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
