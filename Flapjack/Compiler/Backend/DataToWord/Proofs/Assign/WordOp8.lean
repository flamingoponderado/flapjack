module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.WordShift8
@[expose] public section

/-! The Word8 binary-operation assignment case of the data-to-word compiler. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace Op8Witness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end Op8Witness

private theorem byteOpSource {C F : Type} (op : BackendCommon.Opw) (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.wordOp (.wordOpw .w8 op)) values source = .val (result, resultState)) :
    ∃ a b : BitVec 8, values = [.number (Int.ofNat a.toNat), .number (Int.ofNat b.toNat)] ∧
      result = .number (Int.ofNat (ClosSem.applyWordOp op a b).toNat) ∧
      resultState = DataSem.doStack (.wordOp (.wordOpw .w8 op)) values
        (DataSem.doLimSafe source (.wordOp (.wordOpw .w8 op)) values) := by
  cases values with
  | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
  | cons value rest =>
    cases rest with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
    | cons value2 rest =>
      cases rest with
      | cons extra rest => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
      | nil =>
        cases value <;> cases value2 <;>
          simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral]
        rename_i i j
        cases ha : ClosSem.intToByte i with
        | none => simp [ha] at run
        | some a =>
          cases hb : ClosSem.intToByte j with
          | none => simp [ha, hb] at run
          | some b =>
            have ea := (ClosSem.intToByte_iff i a).mp ha
            have eb := (ClosSem.intToByte_iff j b).mp hb
            subst i
            subst j
            simp [ha, hb] at run
            exact ⟨a, b, ⟨rfl, rfl⟩, run.1.symm, run.2.symm⟩

private theorem byteOpRun {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (sec l dest src1 src2 : Nat) (names : Option NumSet)
    (op : BackendCommon.Opw) (a b : BitVec 8) (target : WordSemStateFiniteExact width C F)
    (good : goodDimindex width)
    (found1 : target.getVar (adjustVar src1) = some (.word (smallnum (Int.ofNat a.toNat))))
    (found2 : target.getVar (adjustVar src2) = some (.word (smallnum (Int.ofNat b.toNat)))) :
    WordSemStateFiniteExact.evaluate (assignWordOpW8 op conf sec l dest names src1 src2).1 target =
      (none, target.setVar (adjustVar dest) (.word (smallnum (Int.ofNat (ClosSem.applyWordOp op a b).toNat)))) := by
  simp only [smallnum_byte, bitFourMulEqShift] at found1 found2 ⊢
  rcases good with h | h <;> subst width <;> cases op <;>
    simp [assignWordOpW8, lookupWordOp, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
      wordShiftHOL, wordOpHOL, wordOp, theWords, AndOp.and, OrOp.or, found1, found2, ClosSem.applyWordOp]
  all_goals (congr 2; bv_decide)
/-- A Word8 binary operation satisfies the complete HOL assignment simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_WordOpW8"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignWordOp8_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F) (target : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ opw, op = .wordOp (.wordOpw .w8 opw))
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values) (_depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r, WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q,r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace → stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  obtain ⟨opw, rfl⟩ := opIs
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    obtain ⟨a, b, valuesEq, resultEq, stateEq⟩ := byteOpSource opw values source resultState result run
    subst values
    subst result
    subst resultState
    have argLen := DataSpace.getVars_length args source.locals [.number (Int.ofNat a.toNat), .number (Int.ofNat b.toNat)] argsEq
    cases args with
    | nil => simp at argLen
    | cons arg1 rest =>
      cases rest with
      | nil => simp at argLen
      | cons arg2 rest =>
        cases rest with
        | cons extra rest => simp at argLen
        | nil =>
          obtain ⟨words, getWords, lengthEq⟩ := stateRel_getVars conf l1 l2 source target locs [arg1, arg2]
            [.number (Int.ofNat a.toNat), .number (Int.ofNat b.toNat)] related argsEq
          cases words with
          | nil => simp at lengthEq
          | cons word1 rest =>
            cases rest with
            | nil => simp at lengthEq
            | cons word2 rest =>
              cases rest with
              | cons extra rest => simp at lengthEq
              | nil =>
                let next := DataSem.doStack (.wordOp (.wordOpw .w8 opw))
                  [.number (Int.ofNat a.toNat), .number (Int.ofNat b.toNat)]
                  (DataSem.doLimSafe source (.wordOp (.wordOpw .w8 opw))
                    [.number (Int.ofNat a.toNat), .number (Int.ofNat b.toNat)])
                have nextRel : stateRel conf l1 l2 next target none locs :=
                  stateRel_doStack conf l1 l2 _ target locs _ _
                    (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
                let locals := joinEnv next.locals (sptToAList (sptInter target.locals (adjustSet next.locals)))
                let envs := [(theGlobal next.global, holFapply target.store .globals)] ++ flatStack next.stack target.stack
                have hmem := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                have roots := memoryRel_lookupVars conf target.be (holThe next.tstamps) next.refs next.space
                  target.store target.memory target.mdomain next.locals target envs [arg1, arg2]
                  [.number (Int.ofNat a.toNat), .number (Int.ofNat b.toNat)] [word1, word2] (by
                    refine ⟨?_, ?_, getWords⟩
                    · simpa [locals, envs] using hmem
                    · simpa [next, DataSem.doStack, DataSem.doLimSafe] using argsEq)
                have good := nextRel.2.2.2.2.2.2.1
                have root1 : memoryRel conf target.be (holThe next.tstamps) next.refs next.space
                    target.store target.memory target.mdomain
                    ((.number (Int.ofNat a.toNat), word1) :: (.number (Int.ofNat b.toNat), word2) :: locals ++ envs) := by
                  simpa [locals, envs, List.append_assoc] using roots
                have root2 := memoryRel_tl conf target.be (holThe next.tstamps) next.refs next.space
                  target.store target.memory target.mdomain (.number (Int.ofNat a.toNat), word1)
                  ((.number (Int.ofNat b.toNat), word2) :: locals ++ envs) root1
                have eq1 := memoryRel_numberImp conf target.be (holThe next.tstamps) next.refs next.space
                  target.store target.memory target.mdomain (Int.ofNat a.toNat) word1 _ ⟨good, smallInt_byte good a, root1⟩
                have eq2 := memoryRel_numberImp conf target.be (holThe next.tstamps) next.refs next.space
                  target.store target.memory target.mdomain (Int.ofNat b.toNat) word2 _ ⟨good, smallInt_byte good b, root2⟩
                subst word1
                subst word2
                have bothReads : target.getVar (adjustVar arg1) = some (.word (smallnum (Int.ofNat a.toNat))) ∧
                    target.getVar (adjustVar arg2) = some (.word (smallnum (Int.ofNat b.toNat))) := by
                  cases h1 : target.getVar (adjustVar arg1) <;> cases h2 : target.getVar (adjustVar arg2) <;>
                    simp_all [WordSemStateFiniteExact.getVars]
                let answer := ClosSem.applyWordOp opw a b
                have answerRoot : memoryRel conf target.be (holThe next.tstamps) next.refs next.space
                    target.store target.memory target.mdomain
                    ((.number (Int.ofNat answer.toNat), .word (smallnum (Int.ofNat answer.toNat))) :: locals ++ envs) := by
                  apply impMemoryRel_number conf target.be (holThe next.tstamps) next.refs next.space
                    target.store target.memory target.mdomain (locals ++ envs) _
                  exact ⟨good, smallInt_byte good answer, by simpa [locals, envs] using hmem⟩
                have updated := stateRel_insertRoot conf l1 l2 next target locs dest
                  (.number (Int.ofNat answer.toNat)) (.word (smallnum (Int.ofNat answer.toNat))) nextRel (by
                    simpa [locals, envs] using answerRoot)
                refine ⟨none, target.setVar (adjustVar dest) (.word (smallnum (Int.ofNat answer.toNat))), ?_, by simp, ?_⟩
                · simpa [compileAssign, DataToWord.arg2, answer] using
                    byteOpRun conf n l dest arg1 arg2 none opw a b target good bothReads.1 bothReads.2
                · intro _
                  exact ⟨updated, rfl⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
