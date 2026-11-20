module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BoolTest
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.ShiftVar
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteBitwise
@[expose] public section

/-! The Word8 shift assignment case of the data-to-word compiler. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace Shift8Witness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end Shift8Witness

private theorem shift8Source {C F : Type} (sh : Shift) (amount : Nat) (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.wordOp (.wordShift .w8 sh amount)) values source = .val (result, resultState)) :
    ∃ byte : BitVec 8, values = [.number (Int.ofNat byte.toNat)] ∧
      result = .number (Int.ofNat (shift8Lookup sh byte amount).toNat) ∧
      resultState = DataSem.doStack (.wordOp (.wordShift .w8 sh amount)) values
        (DataSem.doLimSafe source (.wordOp (.wordShift .w8 sh amount)) values) := by
  cases values with
  | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
  | cons value rest =>
    cases rest with
    | cons extra rest => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
    | nil =>
      cases value with
      | number i =>
        cases h : ClosSem.intToByte i with
        | none => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral, h] at run
        | some byte =>
          have eq : i = (byte.toNat : Int) := (ClosSem.intToByte_iff i byte).mp h
          subst i
          simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral, h] at run
          exact ⟨byte, rfl, run.1.symm, run.2.symm⟩
      | word64 _ | block _ _ _ | codePtr _ | refPtr _ _ =>
        simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run

private theorem byteAsrSat (byte : BitVec 8) (n : Nat) (hn : 8 ≤ n) :
    byte.sshiftRight n = byte.sshiftRight 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_sshiftRight]
  simp [show ¬ n + i < 8 by omega, show ¬ 8 + i < 8 by omega]

private theorem byteShiftRun {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (sec l dest src : Nat) (names : Option NumSet)
    (sh : Shift) (amount : Nat) (byte : BitVec 8) (target : WordSemStateFiniteExact width C F)
    (good : goodDimindex width)
    (found : target.getVar (adjustVar src) = some (.word (smallnum (Int.ofNat byte.toNat)))) :
    WordSemStateFiniteExact.evaluate (assignWordShiftW8 sh amount conf sec l dest names src).1 target =
      (none, target.setVar (adjustVar dest) (.word (smallnum (Int.ofNat (shift8Lookup sh byte amount).toNat)))) := by
  simp only [smallnum_byte, bitFourMulEqShift] at found ⊢
  rcases good with h | h <;> subst width <;> cases sh with
  | lsl | lsr | asr =>
    by_cases hn : amount < 8
    · interval_cases amount <;>
        simp [assignWordShiftW8, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
          shiftN, wordShiftHOL, found, shift8Lookup]
      all_goals (congr 2; bv_decide)
    · have hn8 : 8 ≤ amount := by omega
      simp [assignWordShiftW8, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
        shiftN, wordShiftHOL, found, shift8Lookup, Nat.min_eq_right hn8,
        BitVec.shiftLeft_eq_zero hn8, BitVec.ushiftRight_eq_zero hn8, byteAsrSat byte amount hn8]
      all_goals (congr 2; bv_decide)
  | ror =>
    simp only [WordSemStateFiniteExact.getVar] at found
    have shiftEq : byte.rotateRight amount = byte.rotateRight (amount % 8) :=
      BitVec.rotateRight_mod_eq_rotateRight.symm
    simp only [shift8Lookup] at ⊢
    rw [shiftEq]
    have bound : amount % 8 < 8 := Nat.mod_lt _ (by decide)
    generalize hmod : amount % 8 = k at *
    interval_cases k <;>
      simp [-BitVec.rotateRight_mod_eq_rotateRight, assignWordShiftW8, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
        WordSemStateFiniteExact.getVar, shiftN, shiftVar, wordShiftHOL, wordOpHOL, wordOp,
        theWords, found, hmod, OrOp.or]
    all_goals (congr 2; bv_decide)

/-- A Word8 shift satisfies the complete HOL assignment simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_WordShiftW8"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignWordShift8_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F) (target : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ sh amount, op = .wordOp (.wordShift .w8 sh amount))
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values) (_depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r, WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q,r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace → stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  obtain ⟨sh, amount, rfl⟩ := opIs
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    obtain ⟨byte, valuesEq, resultEq, stateEq⟩ := shift8Source sh amount values source resultState result run
    subst values
    subst result
    subst resultState
    have argLen := DataSpace.getVars_length args source.locals [.number (Int.ofNat byte.toNat)] argsEq
    cases args with
    | nil => simp at argLen
    | cons arg rest =>
      cases rest with
      | cons extra rest => simp at argLen
      | nil =>
        have sourceFound : DataSem.getVar arg source.locals = some (.number (Int.ofNat byte.toNat)) := by
          cases h : DataSem.getVar arg source.locals <;> simp_all [DataSem.getVars]
        obtain ⟨word, targetFound⟩ :=
          stateRel_getVar conf l1 l2 source target none locs arg _ related sourceFound
        let next := DataSem.doStack (.wordOp (.wordShift .w8 sh amount)) [.number (Int.ofNat byte.toNat)]
          (DataSem.doLimSafe source (.wordOp (.wordShift .w8 sh amount)) [.number (Int.ofNat byte.toNat)])
        have nextRel : stateRel conf l1 l2 next target none locs :=
          stateRel_doStack conf l1 l2 _ target locs _ _
            (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
        let locals := joinEnv next.locals (sptToAList (sptInter target.locals (adjustSet next.locals)))
        let rest := [(theGlobal next.global, holFapply target.store .globals)] ++ flatStack next.stack target.stack
        have hmem := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        have roots := memoryRel_lookupVars conf target.be (holThe next.tstamps) next.refs next.space
          target.store target.memory target.mdomain next.locals target rest [arg]
          [.number (Int.ofNat byte.toNat)] [word] (by
            refine ⟨?_, ?_, ?_⟩
            · simpa [locals, rest] using hmem
            · simpa [next, DataSem.doStack, DataSem.doLimSafe] using argsEq
            · simp [WordSemStateFiniteExact.getVars, targetFound])
        have good := nextRel.2.2.2.2.2.2.1
        have wordEq := memoryRel_numberImp conf target.be (holThe next.tstamps) next.refs next.space
          target.store target.memory target.mdomain (Int.ofNat byte.toNat) word (locals ++ rest)
          ⟨good, smallInt_byte good byte, by simpa [locals] using roots⟩
        subst word
        let answer := shift8Lookup sh byte amount
        have answerRoot : memoryRel conf target.be (holThe next.tstamps) next.refs next.space
            target.store target.memory target.mdomain
            ((.number (Int.ofNat answer.toNat), .word (smallnum (Int.ofNat answer.toNat))) :: locals ++ rest) := by
          apply impMemoryRel_number conf target.be (holThe next.tstamps) next.refs next.space
            target.store target.memory target.mdomain (locals ++ rest) _
          exact ⟨good, smallInt_byte good answer, by simpa [locals, rest] using hmem⟩
        have updated := stateRel_insertRoot conf l1 l2 next target locs dest
          (.number (Int.ofNat answer.toNat)) (.word (smallnum (Int.ofNat answer.toNat))) nextRel (by
            simpa [locals, rest] using answerRoot)
        refine ⟨none, target.setVar (adjustVar dest) (.word (smallnum (Int.ofNat answer.toNat))), ?_, by simp, ?_⟩
        · simpa [compileAssign, DataToWord.arg1, answer] using
            byteShiftRun conf n l dest arg none sh amount byte target good targetFound
        · intro _
          exact ⟨updated, rfl⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
