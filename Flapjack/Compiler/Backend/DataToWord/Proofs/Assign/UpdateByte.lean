module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.DerefByte
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.SetGlobal

@[expose] public section

/-! Byte update in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.SemanticPrimitivesHOL

namespace UpdateByteAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end UpdateByteAssignmentWitness

/-- Invert the successful source update in the HOL assignment proof. -/
private theorem updateByteSourceRun {C F : Type} (source resultState : DataSem.State C F)
    (values : List DataSem.Value) (result : DataSem.Value)
    (run : DataSem.doApp (.memOp .updateByte) values source = .val (result, resultState)) :
    ∃ bit ptr index value flag bytes byte,
      values = [.refPtr bit ptr, .number index, .number value] ∧
      0 ≤ index ∧ index.toNat < bytes.length ∧
      sptLookup ptr source.refs = some (.byteArray flag bytes) ∧
      ClosSem.intToByte value = some byte ∧ result = DataSem.unitValue ∧
      resultState = { (DataSem.doStack (.memOp .updateByte) values
        (DataSem.doLimSafe source (.memOp .updateByte) values)) with
        refs := sptInsert ptr (.byteArray flag (bytes.set index.toNat byte)) source.refs } := by
  cases values with
  | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.doAppAux, DataSem.applyNonFfi] at run
  | cons v vs =>
    cases vs with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi] at run
    | cons w ws =>
      cases ws with
      | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi] at run
      | cons x xs =>
        cases xs with
        | cons y ys => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi] at run
        | nil =>
          cases v <;> cases w <;> cases x <;>
            simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi]
          rename_i bit ptr index value
          have refsEq : (DataSem.doStack (.memOp .updateByte)
              [.refPtr bit ptr, .number index, .number value]
              (DataSem.doLimSafe source (.memOp .updateByte)
                [.refPtr bit ptr, .number index, .number value])).refs = source.refs := rfl
          rw [refsEq] at run
          cases found : sptLookup ptr source.refs with
          | none => simp [found] at run
          | some ref =>
            cases ref with
            | byteArray flag bytes =>
              by_cases bad : index < 0 ∨ bytes.length ≤ index.toNat
              · simp [found, bad] at run
              · cases conv : ClosSem.intToByte value with
                | none => simp [found, conv] at run
                | some byte =>
                  simp [found, bad, conv] at run
                  obtain ⟨rfl, rfl⟩ := run
                  cases flag <;> simp_all <;> omega
            | _ => simp [found] at run

/-- Byte update satisfies the original data-to-word assignment goal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_UpdateByte"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignUpdateByte_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .memOp .updateByte)
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
    obtain ⟨bit, ptr, index, value, flag, bytes, byte, valuesEq, nonneg, bound, found, conv, resultEq, stateEq⟩ :=
      updateByteSourceRun source resultState values result run
    subst values
    subst result
    subst resultState
    have argLen : args.length = 3 := by
      have h := DataSpace.getVars_length args source.locals [.refPtr bit ptr, .number index, .number value] argsEq
      simpa using h.symm
    cases args with
    | nil => simp at argLen
    | cons a args =>
      cases args with
      | nil => simp at argLen
      | cons b args =>
        cases args with
        | nil => simp at argLen
        | cons c args =>
          cases args with
          | cons d rest => simp at argLen
          | nil =>
            obtain ⟨words, getWords, lengthEq⟩ :=
              stateRel_getVars conf l1 l2 source target locs [a,b,c]
                [.refPtr bit ptr, .number index, .number value] related argsEq
            cases words with
            | nil => simp at lengthEq
            | cons word1 words =>
              cases words with
              | nil => simp at lengthEq
              | cons word2 words =>
                cases words with
                | nil => simp at lengthEq
                | cons word3 words =>
                  cases words with
                  | cons word4 rest => simp at lengthEq
                  | nil =>
                    let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
                      flatStack source.stack target.stack
                    have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
                      target.store target.memory target.mdomain target envs [a,b,c]
                      [.refPtr bit ptr, .number index, .number value] [word1,word2,word3] (by
                        refine ⟨?_, argsEq, getWords⟩
                        simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
                    have good := related.2.2.2.2.2.2.1
                    let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
                    obtain ⟨w, address, header, _, wordEq, low, headerEq, _, _, _, _, real,
                      _, _, reads, updates, sizeBound⟩ :=
                      memoryRel_byteArrayImp (β := Unit) conf target.be (holThe source.tstamps) source.refs
                        source.space target.store target.memory target.mdomain bit flag ptr bytes word1
                        ((.number index, word2) :: (.number value, word3) :: locals ++ envs)
                        ⟨by simpa [locals] using roots, found, good⟩
                    have small : smallInt width index := by
                      rcases good with hw | hw <;> subst width <;>
                        simp [smallInt] at sizeBound ⊢ <;> omega
                    have tail := memoryRel_tail conf target.be (holThe source.tstamps) source.refs source.space
                      target.store target.memory target.mdomain (.refPtr bit ptr, word1)
                      ((.number index, word2) :: (.number value, word3) :: locals ++ envs)
                      (by simpa [locals] using roots)
                    have indexEq := memoryRel_numberImp conf target.be (holThe source.tstamps) source.refs
                      source.space target.store target.memory target.mdomain index word2
                      ((.number value, word3) :: locals ++ envs) ⟨good, small, tail⟩
                    have tail2 := memoryRel_tail conf target.be (holThe source.tstamps) source.refs source.space
                      target.store target.memory target.mdomain (.number index, word2)
                      ((.number value, word3) :: locals ++ envs) tail
                    have valueSmall : smallInt width value := by
                      simp [ClosSem.intToByte] at conv
                      rcases good with hw | hw <;> subst width <;> simp [smallInt] <;> omega
                    have valueEq := memoryRel_numberImp conf target.be (holThe source.tstamps) source.refs
                      source.space target.store target.memory target.mdomain value word3 (locals ++ envs)
                      ⟨good, valueSmall, tail2⟩
                    subst word1
                    subst word2
                    subst word3
                    have operands : WordSemStateFiniteExact.getVar (adjustVar a) target = some (.word w) ∧
                        WordSemStateFiniteExact.getVar (adjustVar b) target = some (.word (smallnum index)) ∧
                        WordSemStateFiniteExact.getVar (adjustVar c) target = some (.word (smallnum value)) := by
                      cases h1 : WordSemStateFiniteExact.getVar (adjustVar a) target <;>
                        cases h2 : WordSemStateFiniteExact.getVar (adjustVar b) target <;>
                        cases h3 : WordSemStateFiniteExact.getVar (adjustVar c) target <;>
                        simp_all [WordSemStateFiniteExact.getVars]
                    have valueNonneg : 0 ≤ value := by
                      simp [ClosSem.intToByte] at conv
                      omega
                    have valueByte : (BitVec.ofNat width value.toNat).setWidth 8 = byte := by
                      simp [ClosSem.intToByte] at conv
                      obtain ⟨bounds, rfl⟩ := conv
                      rcases good with hw | hw <;> subst width <;>
                        apply BitVec.eq_of_toNat_eq <;>
                        simp [BitVec.toNat_ofInt] <;> omega
                    have realExp := Bignum.getRealAddr_lemma conf (adjustVar a) target w address
                      ⟨related.2.2.2.2.2.2.2.1, good, operands.1, real⟩
                    have offsetExp := getRealByteOffset_lemma (adjustVar b) target (smallnum index)
                      ⟨operands.2.1, good⟩
                    rw [smallnum_nonneg_shift index good small nonneg] at offsetExp
                    let ad := address + StackRemove.bytesInWord width + BitVec.ofNat width index.toNat
                    have addressExp : WordSemStateFiniteExact.wordExp target
                        (.op .add [realAddr conf (adjustVar a), realByteOffset (adjustVar b)]) =
                        some (.word ad) := by
                      simp [WordSemStateFiniteExact.wordExp, realExp, offsetExp, theWords, wordOpHOL,
                        wordOp, ad, StackRemove.bytesInWord, wordSemBytesInWord, BitVec.add_assoc]
                    have read := reads index.toNat bound
                    let mem := fun key => if key = holByteAlign ad then
                      .word (HolByte.setByte ad byte (wordSemTheWord (target.memory (holByteAlign ad))) target.be)
                      else target.memory key
                    have store : memStoreByteAuxExact target.memory target.mdomain target.be ad byte = some mem := by
                      cases wordAt : target.memory (holByteAlign ad) with
                      | loc x y =>
                        simp [memLoadByteAuxExact, riscvByteAlignHOL_eq good, wordAt, ad] at read
                      | word x =>
                        have inside : target.mdomain (holByteAlign ad) = true := by
                          by_cases h : target.mdomain (holByteAlign ad) = true
                          · exact h
                          · simp [memLoadByteAuxExact, riscvByteAlignHOL_eq good, wordAt, h, ad] at read
                        simp [memStoreByteAuxExact, riscvByteAlignHOL_eq good, wordAt, inside,
                          wordSemTheWord, setByteHOL8_eq, mem]
                    let refs := sptInsert ptr (.byteArray flag (bytes.set index.toNat byte)) source.refs
                    have updateHeap := updates index.toNat byte bound
                    have updateTail1 := memoryRel_tail conf target.be (holThe source.tstamps) refs source.space
                      target.store mem target.mdomain (.refPtr bit ptr, .word w)
                      ((.number index, .word (smallnum index)) :: (.number value, .word (smallnum value)) :: locals ++ envs)
                      (by simpa [mem, refs, ad] using updateHeap)
                    have updateTail2 := memoryRel_tail conf target.be (holThe source.tstamps) refs source.space
                      target.store mem target.mdomain (.number index, .word (smallnum index))
                      ((.number value, .word (smallnum value)) :: locals ++ envs) updateTail1
                    have baseHeap := memoryRel_tail conf target.be (holThe source.tstamps) refs source.space
                      target.store mem target.mdomain (.number value, .word (smallnum value))
                      (locals ++ envs) updateTail2
                    let next := DataSem.doStack (.memOp .updateByte)
                      [.refPtr bit ptr, .number index, .number value]
                      (DataSem.doLimSafe source (.memOp .updateByte)
                        [.refPtr bit ptr, .number index, .number value])
                    have nextRel : stateRel conf l1 l2 next target none locs :=
                      stateRel_doStack conf l1 l2 _ target locs _ _
                        (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
                    let midSource := {next with refs := refs}
                    let midTarget := {target with memory := mem}
                    have midRel : stateRel conf l1 l2 midSource midTarget none locs :=
                      stateRel_replaceMemory conf l1 l2 next target locs refs mem nextRel (by
                        simpa [next, DataSem.doStack, DataSem.doLimSafe, locals, envs] using baseHeap)
                    let s1 := WordSemStateFiniteExact.setVar 1 (.word ad) target
                    let s3 := WordSemStateFiniteExact.setVar 3 (.word (BitVec.ofNat width value.toNat)) s1
                    let stored := {s3 with memory := mem}
                    let final := WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) stored
                    have valueShift := smallnum_nonneg_shift value good valueSmall valueNonneg
                    have store' : memStoreByteAuxExact target.memory target.mdomain target.be
                        (address + (wordSemBytesInWord + BitVec.ofNat width index.toNat)) byte = some mem := by
                      simpa [ad, StackRemove.bytesInWord, wordSemBytesInWord, BitVec.add_assoc] using store
                    simp only [adjustVar] at realExp offsetExp operands
                    simp only [WordSemStateFiniteExact.getVar] at operands
                    have eval : WordSemStateFiniteExact.evaluate
                        (compileAssign conf n l dest (.memOp .updateByte) [a,b,c] none).1 target =
                        (none, final) := by
                      simp [compileAssign, arg3, assignUpdateByte, unitExp, wordListSeq,
                        WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
                        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.fixClock,
                        WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                        sptLookup_sptInsert_ne, adjustVar,
                        shiftN, theWords, wordOpHOL, wordOp, wordShiftHOL,
                        realExp, offsetExp, operands, ad, s1, s3, stored, final,
                        BitVec.add_assoc]
                      rcases good with hw | hw <;> subst width <;>
                        simp_all [sptLookup_sptInsert_ne, sptLookup_sptInsert_same,
                          wordSemBytesInWord, StackRemove.bytesInWord]
                    have mid3Rel : stateRel conf l1 l2 midSource
                        (WordSemStateFiniteExact.setVar 3 (.word (BitVec.ofNat width value.toNat))
                          (WordSemStateFiniteExact.setVar 1 (.word ad) midTarget)) none locs := by
                      change stateRel conf l1 l2 midSource
                        { (WordSemStateFiniteExact.setVar 1 (.word ad) midTarget) with
                          locals := sptInsert 3 (.word (BitVec.ofNat width value.toNat))
                            (WordSemStateFiniteExact.setVar 1 (.word ad) midTarget).locals } none locs
                      rw [stateRel_insertOdd conf l1 l2 midSource _ none locs 3 _ (by decide)]
                      simpa [WordSemStateFiniteExact.setVar, stateRel_insertOdd] using midRel
                    have storedRel : stateRel conf l1 l2 midSource stored none locs := by
                      simpa [stored, s3, s1, midTarget, WordSemStateFiniteExact.setVar] using mid3Rel
                    have heap := storedRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                    have unitRoot := memoryRel_unit conf stored.be (holThe midSource.tstamps) midSource.refs midSource.space
                      stored.store stored.memory stored.mdomain
                      (joinEnv midSource.locals (sptToAList (sptInter stored.locals (adjustSet midSource.locals))) ++
                        [(theGlobal midSource.global, holFapply stored.store .globals)] ++ flatStack midSource.stack stored.stack)
                      ⟨heap, storedRel.2.2.2.2.2.2.1⟩
                    have finalRel := stateRel_insertRoot conf l1 l2 midSource stored locs dest DataSem.unitValue
                      (.word 2) storedRel unitRoot
                    refine ⟨none, final, eval, ?_, ?_⟩
                    · simp
                    · intro _
                      simpa [final, midSource, refs, next, DataSem.doStack, DataSem.doLimSafe] using finalRel

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
