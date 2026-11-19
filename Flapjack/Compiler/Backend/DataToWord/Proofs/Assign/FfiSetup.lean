module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.FfiInputs
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutOdd
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteArrayWrite
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Space
public import Flapjack.FfiBridge

@[expose] public section

/-! Execution of the argument setup used by the FFI assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- The setup, successful foreign call and post-call memory relation used in
the HOL FFI assignment proof. This factoring has no separate HOL declaration.
Both empty and nonempty names are covered. The compiler emits
this setup only when `conf.callEmptyFfi` is true or `name` is nonempty; the
other branch emits a direct unit assignment instead. -/
theorem ffi_success_setup_call {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source cut resultState : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : NumSet) (args : List Nat) (values : List DataSem.Value)
    (name : Basis.Pure.MlString.MlString) (result : DataSem.Value)
    (related : stateRel conf l1 l2 source target none locs)
    (cutRun : DataSem.cutStateOpt (some names) source = some cut)
    (read : DataSem.getVars args source.locals = some values)
    (run : DataSem.doApp (.ffi name) values cut = .val (result, resultState)) :
    ∃ (firstVar secondVar first second : Nat)
      (config bytes updated : List (BitVec 8)) (ffi : HolFfiState F)
      (address1 address2 : BitVec width) (wordCut : Spt (WordLocW width)),
      args = [firstVar, secondVar] ∧
      sptLookup first source.refs = some (.byteArray true config) ∧
      sptLookup second source.refs = some (.byteArray false bytes) ∧
      callFFIHOL source.ffi (.extCall name) config bytes = .ret ffi updated ∧
      updated.length = bytes.length ∧
      readBytearrayGenericHOL (address1 + StackRemove.bytesInWord width) config.length
        (memLoadByteAuxExact target.memory target.mdomain target.be) = some config ∧
      readBytearrayGenericHOL (address2 + StackRemove.bytesInWord width) bytes.length
        (memLoadByteAuxExact target.memory target.mdomain target.be) = some bytes ∧
      let empty := name == Basis.Pure.MlString.ofString ""
      let ptr1 := address1 + wordSemBytesInWord
      let len1 := BitVec.ofNat width config.length
      let ptr2 := if empty then 0 else address2 + wordSemBytesInWord
      let len2 := if empty then 0 else BitVec.ofNat width bytes.length
      WordSemStateFiniteExact.evaluate (wordListSeq [
        .assign 1 (.op .add [realAddr conf (adjustVar firstVar), .const wordSemBytesInWord]),
        .assign 3 (.op .sub [shiftN .lsr (.load (realAddr conf (adjustVar firstVar)))
          (width - wordShiftAmount width - conf.lenSize), .const wordSemBytesInWord]),
        .assign 5 (if empty then .const 0 else
          .op .add [realAddr conf (adjustVar secondVar), .const wordSemBytesInWord]),
        .assign 7 (if empty then .const 0 else
          .op .sub [shiftN .lsr (.load (realAddr conf (adjustVar secondVar)))
            (width - wordShiftAmount width - conf.lenSize), .const wordSemBytesInWord])]) target =
        (none, { target with locals := (sptInsert 7 (.word len2)
          (sptInsert 5 (.word ptr2) (sptInsert 3 (.word len1)
            (sptInsert 1 (.word ptr1) target.locals)))) }) ∧
      wordSemCutEnv (adjustSets names) target.locals = some wordCut ∧
      stateRel conf l1 l2 cut { target with locals := wordCut } none locs ∧
      WordSemStateFiniteExact.evaluate (.ffi name 1 3 5 7 (adjustSets names))
        { target with locals := (sptInsert 7 (.word len2)
          (sptInsert 5 (.word ptr2) (sptInsert 3 (.word len1)
            (sptInsert 1 (.word ptr1) target.locals)))) } =
        (none, { target with locals := wordCut, fpRegs := HolFiniteMapExact.empty, ffi := ffi, memory := (if empty then target.memory else writeBytearrayExact ptr2 updated target.memory target.mdomain target.be) }) ∧
      Memory.memoryRel conf target.be (holThe source.tstamps)
        (sptInsert second (.byteArray false updated) source.refs) 0 target.store
        (if empty then target.memory else
          writeBytearrayExact (address2 + wordSemBytesInWord) updated target.memory target.mdomain target.be)
        target.mdomain
        (joinEnv cut.locals (sptToAList (sptInter wordCut (adjustSet cut.locals))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++
          flatStack source.stack target.stack) := by
  obtain ⟨firstVar, secondVar, flag1, flag2, first, second, config, bytes, updated, ffi,
    firstWord, secondWord, argsEq, valuesEq, wordRead, firstRead, secondRead, call,
    lengthEq, roots, w1, w2, address1, address2, header1, header2, loc1, loc2,
    real1, real2, mem1, mem2, configRead, bytesRead, bound1, bound2, decoded1,
    decoded2, addressEval, ptrEval, afterTemps⟩ :=
    ffi_success_inputs conf l1 l2 source cut resultState target locs names args values name result
      related cutRun read run
  obtain ⟨wordCut, words, wordCutRun, wordsRun, sourceLen, targetLen, cutRelated, cutWordRelated⟩ :=
    stateRel_cutStateOpt_some conf l1 l2 source target locs args values names cut ⟨related, read, cutRun⟩
  refine ⟨firstVar, secondVar, first, second, config, bytes, updated, ffi, address1, address2, wordCut,
    argsEq, firstRead, secondRead, call, lengthEq, configRead, bytesRead, ?_, wordCutRun, cutWordRelated, ?_, ?_⟩
  · try dsimp only
    cases empty : (name == Basis.Pure.MlString.ofString "") <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals
      have facts := afterTemps (.word (address1 + wordSemBytesInWord))
        (.word (BitVec.ofNat width config.length))
        (.word (if name == Basis.Pure.MlString.ofString "" then 0 else address2 + wordSemBytesInWord))
      simp only [empty, Bool.false_eq_true, ↓reduceIte] at facts
      obtain ⟨length1, address2Eval, ptr2Eval, length2⟩ := facts
      simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.wordExp,
        WordSemStateFiniteExact.fixClock, ptrEval, length1, ptr2Eval, length2]
  · try dsimp only
    have ffiEq : target.ffi = source.ffi := related.1
    have len1 : (BitVec.ofNat width config.length).toNat = config.length := by
      simpa only [decoded1.1] using decoded1.2
    have len2 : (BitVec.ofNat width bytes.length).toNat = bytes.length := by
      simpa only [decoded2.1] using decoded2.2
    have configRead' : readBytearrayGenericHOL (address1 + BitVec.ofNat width (width / 8)) config.length
        (memLoadByteAuxExact target.memory target.mdomain target.be) = some config := by
      simpa [StackRemove.bytesInWord] using configRead
    have bytesRead' : readBytearrayGenericHOL (address2 + BitVec.ofNat width (width / 8)) bytes.length
        (memLoadByteAuxExact target.memory target.mdomain target.be) = some bytes := by
      simpa [StackRemove.bytesInWord] using bytesRead
    have cutTemps : ∀ (v1 v3 v5 v7 : WordLocW width),
        wordSemCutEnv (adjustSets names)
          (sptInsert 7 v7 (sptInsert 5 v5 (sptInsert 3 v3 (sptInsert 1 v1 target.locals)))) =
            some wordCut := by
      intro v1 v3 v5 v7
      simp [cutEnv_adjustSets_insertOdd, wordCutRun]
    cases empty : (name == Basis.Pure.MlString.ofString "") with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne, cutTemps,
        readBytearrayWordHOL, wordSemBytesInWord,
        len1, len2, configRead', bytesRead', ffiEq, call]
    | true =>
      have nameEq : name = Basis.Pure.MlString.ofString "" := by simpa using empty
      have ffiReturn : ffi = source.ffi := by
        rw [nameEq] at call
        have eqs : ffi = source.ffi ∧ updated = bytes := by
          simpa [Basis.Pure.MlString.ofString, callFFIHOL_empty_extCall] using call.symm
        exact eqs.1
      simp only [↓reduceIte]
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne, cutTemps,
        readBytearrayWordHOL, readBytearrayGenericHOL, wordSemBytesInWord,
        len1, configRead', ffiEq, nameEq, Basis.Pure.MlString.ofString,
        callFFIHOL_empty_extCall, writeBytearrayExact, ffiReturn]
  · have good := related.2.2.2.2.2.2.1
    have zeroRoots := Memory.memoryRel_zeroSpace conf target.be (holThe source.tstamps) source.refs
      source.space target.store target.memory target.mdomain _ roots
    have tailRoots := Memory.memoryRel_tl conf target.be (holThe source.tstamps) source.refs
      0 target.store target.memory target.mdomain _ _ zeroRoots
    obtain ⟨w, address, header, _, loc, _, _, _, _, _, simple, real, _, _, _, _, _⟩ :=
      Memory.memoryRel_byteArrayImp (β := Unit) conf target.be (holThe source.tstamps)
        source.refs 0 target.store target.memory target.mdomain flag2 false second bytes
        secondWord _ ⟨tailRoots, secondRead, good⟩
    have wEq : w = w2 := WordLocW.word.inj (loc.symm.trans loc2)
    subst w
    have addrEq : address = address2 := Option.some.inj (real.symm.trans real2)
    subst address
    rw [loc2] at tailRoots
    have updatedRoots := Memory.memoryRel_writeBytearray conf target.be (holThe source.tstamps)
      0 target.store target.mdomain flag2 second w2 address2 _ updated bytes target.memory source.refs
      ⟨tailRoots, secondRead, lengthEq, simple, good⟩
    have updatedTail := Memory.memoryRel_tl conf target.be (holThe source.tstamps) _ 0 target.store _ target.mdomain
      _ _ updatedRoots
    have rootSubset : ∀ pair,
        pair ∈ (joinEnv cut.locals (sptToAList (sptInter wordCut (adjustSet cut.locals))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack) →
        pair ∈ (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack) := by
      intro pair member
      simp only [List.mem_append] at member ⊢
      rcases member with (member | member) | member
      · apply Or.inl
        apply Or.inl
        apply joinEnv_submap_mem cut.locals source.locals wordCut target.locals pair
        refine ⟨?_, ?_, member⟩
        · intro key value found
          have cutEq := cutStateOpt_some_eq names source cut cutRun
          rw [cutEq] at found
          simp only [sptLookup_mkWf, sptLookup_sptInterCases] at found
          cases original : sptLookup key source.locals with
          | none => simp [original] at found
          | some originalValue =>
            cases retained : sptLookup key names with
            | none => simp [original, retained] at found
            | some entry => simpa [original, retained] using found
        · intro key value found
          exact cutEnv_lookup (adjustSets names) target.locals wordCut key value ⟨wordCutRun, found⟩
      · exact Or.inl (Or.inr member)
      · exact Or.inr member
    cases empty : (name == Basis.Pure.MlString.ofString "") with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) _ 0 target.store _ target.mdomain _ _ rootSubset
      simpa [wordSemBytesInWord, StackRemove.bytesInWord] using updatedTail
    | true =>
      simp only [↓reduceIte]
      have nameEq : name = Basis.Pure.MlString.ofString "" := by simpa using empty
      have updatedEq : updated = bytes := by
        rw [nameEq] at call
        have eqs : ffi = source.ffi ∧ updated = bytes := by
          simpa [Basis.Pure.MlString.ofString, callFFIHOL_empty_extCall] using call.symm
        exact eqs.2
      rw [updatedEq, sptInsertUnchanged source.refs second (.byteArray false bytes) secondRead]
      have originalTail := Memory.memoryRel_tl conf target.be (holThe source.tstamps) source.refs
        0 target.store target.memory target.mdomain _ _ tailRoots
      exact Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs 0
        target.store target.memory target.mdomain _ _ rootSubset originalTail

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
