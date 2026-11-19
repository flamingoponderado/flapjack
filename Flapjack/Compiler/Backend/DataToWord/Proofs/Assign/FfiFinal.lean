module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.FfiSetup

@[expose] public section

/-! FFI final-event assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.BackendProps

namespace assignFfiFinalMap
/-- Canonical target-state roundtrip for the assignment simulation. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end assignFfiFinalMap

/-- The complete FFI final-event assignment theorem. The evaluator inherits
the real-model assumption recorded in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_FFI_final"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignFfi_final {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (source cut : Flapjack.Compiler.Backend.DataSem.State C F) (target : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (name : Basis.Pure.MlString.MlString)
    (args : List Nat) (names : Option NumSet) (values : List Flapjack.Compiler.Backend.DataSem.Value) (event : HolFinalEvent)
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames (.ffi name) ≠ names.isNone)
    (cutRun : DataSem.cutStateOpt names source = some cut)
    (read : DataSem.getVars args source.locals = some values)
    (_depth : target.termdep > 1)
    (run : DataSem.doApp (.ffi name) values cut = .err (.abort (.ffiError event))) :
    ∃ q r,
      WordSemStateFiniteExact.evaluate (compileAssign conf n l dest (.ffi name) args names).1 target = (q, r) ∧
      optionLe r.stackMax source.stackMax ∧ q ≠ some .notEnoughSpace ∧ r.ffi = target.ffi ∧
      q = some (.finalFfi event) := by
  cases names with
  | none => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | some names =>
    obtain ⟨flag1, flag2, first, second, config, bytes, valuesEq, firstCut, secondCut, callCut, notEmpty⟩ :=
      doApp_ffi_final name values cut event run
    have cutEq := cutStateOpt_some_eq names source cut cutRun
    have firstRead : sptLookup first source.refs = some (.byteArray true config) := by simpa [cutEq] using firstCut
    have secondRead : sptLookup second source.refs = some (.byteArray false bytes) := by simpa [cutEq] using secondCut
    have call : callFFIHOL source.ffi (.extCall name) config bytes = .final event := by simpa [cutEq] using callCut
    obtain ⟨firstVar, secondVar, firstWord, secondWord, argsShape, wordRead, roots,
      w1, w2, address1, address2, header1, header2, loc1, loc2, real1, real2, mem1, mem2,
      configRead, bytesRead, bound1, bound2, decoded1, decoded2, addressEval, ptrEval, afterTemps⟩ :=
      ffi_reference_inputs conf l1 l2 source target locs args values flag1 flag2 first second config bytes
        related read valuesEq firstRead secondRead
    obtain ⟨wordCut, words, wordCutRun, wordsRun, sourceLen, targetLen, cutRelated, cutWordRelated⟩ :=
      stateRel_cutStateOpt_some conf l1 l2 source target locs args values names cut ⟨related, read, cutRun⟩
    let ptr1 := address1 + wordSemBytesInWord
    let len1 := BitVec.ofNat width config.length
    let ptr2 := address2 + wordSemBytesInWord
    let len2 := BitVec.ofNat width bytes.length
    let mid := { target with locals := (sptInsert 7 (.word len2) (sptInsert 5 (.word ptr2) (sptInsert 3 (.word len1) (sptInsert 1 (.word ptr1) target.locals)))) }
    have ⟨firstLength, secondAddr, secondPtr, secondLength⟩ := afterTemps (.word ptr1) (.word len1) (.word ptr2)
    have setupRun : WordSemStateFiniteExact.evaluate (wordListSeq [
        .assign 1 (.op .add [realAddr conf (adjustVar firstVar), .const wordSemBytesInWord]),
        .assign 3 (.op .sub [shiftN .lsr (.load (realAddr conf (adjustVar firstVar)))
          (width - wordShiftAmount width - conf.lenSize), .const wordSemBytesInWord]),
        .assign 5 (.op .add [realAddr conf (adjustVar secondVar), .const wordSemBytesInWord]),
        .assign 7 (.op .sub [shiftN .lsr (.load (realAddr conf (adjustVar secondVar)))
          (width - wordShiftAmount width - conf.lenSize), .const wordSemBytesInWord])]) target = (none, mid) := by
      simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.fixClock, ptrEval, firstLength,
        secondPtr, secondLength, mid, ptr1, len1, ptr2, len2]
    have len1Nat : len1.toNat = config.length := by simpa only [len1, decoded1.1] using decoded1.2
    have len2Nat : len2.toNat = bytes.length := by simpa only [len2, decoded2.1] using decoded2.2
    have configRead' : readBytearrayGenericHOL ptr1 config.length
        (memLoadByteAuxExact target.memory target.mdomain target.be) = some config := by
      simpa [ptr1, wordSemBytesInWord, StackRemove.bytesInWord] using configRead
    have bytesRead' : readBytearrayGenericHOL ptr2 bytes.length
        (memLoadByteAuxExact target.memory target.mdomain target.be) = some bytes := by
      simpa [ptr2, wordSemBytesInWord, StackRemove.bytesInWord] using bytesRead
    have cutTemps : wordSemCutEnv (adjustSets names) mid.locals = some wordCut := by
      simp [mid, cutEnv_adjustSets_insertOdd, wordCutRun]
    have callRun : WordSemStateFiniteExact.evaluate (.ffi name 1 3 5 7 (adjustSets names)) mid =
        (some (.finalFfi event), WordSemStateFiniteExact.flushState true mid) := by
      have ffiEq : target.ffi = source.ffi := related.1
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar, mid,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne, cutTemps,
        readBytearrayWordHOL, len1Nat, len2Nat, configRead', bytesRead', ffiEq, call]
    have seqRun : WordSemStateFiniteExact.evaluate (wordListSeq [
        .assign 1 (.op .add [realAddr conf (adjustVar firstVar), .const wordSemBytesInWord]),
        .assign 3 (.op .sub [shiftN .lsr (.load (realAddr conf (adjustVar firstVar)))
          (width - wordShiftAmount width - conf.lenSize), .const wordSemBytesInWord]),
        .assign 5 (.op .add [realAddr conf (adjustVar secondVar), .const wordSemBytesInWord]),
        .assign 7 (.op .sub [shiftN .lsr (.load (realAddr conf (adjustVar secondVar)))
          (width - wordShiftAmount width - conf.lenSize), .const wordSemBytesInWord]),
        .ffi name 1 3 5 7 (adjustSets names), .assign (adjustVar dest) (.const 2)]) target =
          (some (.finalFfi event), WordSemStateFiniteExact.flushState true mid) := by
      change WordSemStateFiniteExact.evaluate (wordListSeq [
        .assign 1 (.op .add [realAddr conf (adjustVar firstVar), .const wordSemBytesInWord]),
        .assign 3 (.op .sub [shiftN .lsr (.load (realAddr conf (adjustVar firstVar)))
          (width - wordShiftAmount width - conf.lenSize), .const wordSemBytesInWord]),
        .assign 5 (.op .add [realAddr conf (adjustVar secondVar), .const wordSemBytesInWord]),
        .assign 7 (.op .sub [shiftN .lsr (.load (realAddr conf (adjustVar secondVar)))
          (width - wordShiftAmount width - conf.lenSize), .const wordSemBytesInWord]),
        wordListSeq [.ffi name 1 3 5 7 (adjustSets names), .assign (adjustVar dest) (.const 2)]]) target = _
      rw [evaluate_four_assign_append _ _ _ _ _ _ _ setupRun]
      change WordSemStateFiniteExact.evaluate
        (.seq (.ffi name 1 3 5 7 (adjustSets names)) (.assign (adjustVar dest) (.const 2))) mid = _
      rw [WordSemStateFiniteExact.evaluate, callRun]
      simp [WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.flushState]
    refine ⟨some (.finalFfi event), WordSemStateFiniteExact.flushState true mid, ?_, ?_, by simp, ?_, rfl⟩
    · simpa [compileAssign, arg2, assignFfi, argsShape, notEmpty] using seqRun
    · have stackBound := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simpa [WordSemStateFiniteExact.flushState, mid] using stackBound
    · rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
