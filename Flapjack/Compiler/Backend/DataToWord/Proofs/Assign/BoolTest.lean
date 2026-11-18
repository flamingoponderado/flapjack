module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BoolNot

@[expose] public section

/-! Boolean equality in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps

namespace assignBoolTestMap
/-- Canonical target-state roundtrip for the assignment simulation. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end assignBoolTestMap

/-- A successful source Boolean decode is an empty block tagged zero or one.
This factors the `dest_Boolv` case analysis in the HOL assignment proof. -/
private theorem destBool_shape (value : DataSem.Value) (b : Bool)
    (decoded : DataSem.destBool value = some b) :
    ∃ stamp tag, value = .block stamp tag [] ∧ tag < 2 ∧ b = decide (tag = 1) := by
  cases value with
  | block stamp tag xs =>
    by_cases h : xs = [] ∧ tag < 2
    · obtain ⟨rfl, bound⟩ := h
      refine ⟨stamp, tag, rfl, bound, ?_⟩
      simpa [DataSem.destBool, bound] using decoded.symm
    · simp [DataSem.destBool] at decoded
      exact (h ⟨decoded.1.1, by omega⟩).elim
  | number n => simp [DataSem.destBool] at decoded
  | word64 w => simp [DataSem.destBool] at decoded
  | codePtr p => simp [DataSem.destBool] at decoded
  | refPtr t p => simp [DataSem.destBool] at decoded

/-- Boolean equality satisfies the original data-to-word assignment goal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_BoolTest"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignBoolTest_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (result : Flapjack.Compiler.Backend.DataSem.Value)
    (boolOp : ∃ test, op = .blockOp (.boolTest test))
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
  obtain ⟨test, rfl⟩ := boolOp
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    cases values with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi] at run
    | cons first rest =>
      cases rest with
      | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi] at run
      | cons second rest =>
        cases rest with
        | cons extra rest => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi] at run
        | nil =>
          cases firstDecode : DataSem.destBool first with
          | none => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi, firstDecode] at run
          | some a =>
            cases secondDecode : DataSem.destBool second with
            | none => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
                DataSem.doAppAux, DataSem.applyNonFfi, firstDecode, secondDecode] at run
            | some b =>
              obtain ⟨stamp1, tag1, rfl, bound1, rfl⟩ := destBool_shape first a firstDecode
              obtain ⟨stamp2, tag2, rfl, bound2, rfl⟩ := destBool_shape second b secondDecode
              simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
                DataSem.doAppAux, DataSem.applyNonFfi, firstDecode, secondDecode] at run
              obtain ⟨rfl, rfl⟩ := run
              have argLen : args.length = 2 := by
                have h := DataSpace.getVars_length args source.locals
                  [.block stamp1 tag1 [], .block stamp2 tag2 []] argsEq
                simpa using h.symm
              cases args with
              | nil => simp at argLen
              | cons arg1 args =>
                cases args with
                | nil => simp at argLen
                | cons arg2 args =>
                  cases args with
                  | cons extra args => simp at argLen
                  | nil =>
                    have found : DataSem.getVar arg1 source.locals = some (.block stamp1 tag1 []) ∧
                        DataSem.getVar arg2 source.locals = some (.block stamp2 tag2 []) := by
                      cases h1 : DataSem.getVar arg1 source.locals <;>
                        cases h2 : DataSem.getVar arg2 source.locals <;>
                        simp_all [DataSem.getVars]
                    obtain ⟨w1, hw1⟩ := stateRel_getVar conf l1 l2 source target none locs arg1 _ related found.1
                    obtain ⟨w2, hw2⟩ := stateRel_getVar conf l1 l2 source target none locs arg2 _ related found.2
                    let next := DataSem.doStack (.blockOp (.boolTest test))
                      [.block stamp1 tag1 [], .block stamp2 tag2 []]
                      (DataSem.doLimSafe source (.blockOp (.boolTest test))
                        [.block stamp1 tag1 [], .block stamp2 tag2 []])
                    have nextRel : stateRel conf l1 l2 next target none locs :=
                      stateRel_doStack conf l1 l2 _ target locs _ _
                        (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
                    let locals := joinEnv next.locals (sptToAList (sptInter target.locals (adjustSet next.locals)))
                    let rest := [(theGlobal next.global, holFapply target.store .globals)] ++ flatStack next.stack target.stack
                    have hmem := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                    have roots := memoryRel_lookupVars conf target.be (holThe next.tstamps) next.refs next.space
                      target.store target.memory target.mdomain next.locals target rest [arg1, arg2]
                      [.block stamp1 tag1 [], .block stamp2 tag2 []] [w1, w2] (by
                        refine ⟨?_, ?_, ?_⟩
                        · simpa [locals, rest] using hmem
                        · simpa [next, DataSem.doStack, DataSem.doLimSafe] using argsEq
                        · simp [WordSemStateFiniteExact.getVars, hw1, hw2])
                    have good := nextRel.2.2.2.2.2.2.1
                    have enc1 := boolBlock_word conf target.be (holThe next.tstamps) next.refs next.space
                      target.store target.memory target.mdomain stamp1 tag1 w1
                      ((.block stamp2 tag2 [], w2) :: locals ++ rest)
                      (by simpa [locals] using roots) good
                    have tail := memoryRel_tail conf target.be (holThe next.tstamps) next.refs next.space
                      target.store target.memory target.mdomain (.block stamp1 tag1 [], w1)
                      ((.block stamp2 tag2 [], w2) :: locals ++ rest) (by simpa [locals] using roots)
                    have enc2 := boolBlock_word conf target.be (holThe next.tstamps) next.refs next.space
                      target.store target.memory target.mdomain stamp2 tag2 w2 (locals ++ rest) tail good
                    subst w1
                    subst w2
                    let answer := (decide (tag1 = 1) == decide (tag2 = 1))
                    let out : BitVec width := if answer then 18 else 2
                    have boolSame : ((BitVec.ofNat width tag1 * (16 : BitVec width) + 2) ==
                        (BitVec.ofNat width tag2 * (16 : BitVec width) + 2)) = answer := by
                      have t1 : tag1 = 0 ∨ tag1 = 1 := by omega
                      have t2 : tag2 = 0 ∨ tag2 = 1 := by omega
                      rcases t1 with rfl | rfl <;> rcases t2 with rfl | rfl <;>
                        rcases good with h | h <;> subst width <;> decide
                    change ((BitVec.ofNat width tag1 * 16#width + 2#width) ==
                      (BitVec.ofNat width tag2 * 16#width + 2#width)) = answer at boolSame
                    have boolRoot : memoryRel conf target.be (holThe next.tstamps) next.refs next.space
                        target.store target.memory target.mdomain
                        ((DataSem.boolValue answer, .word out) :: locals ++ rest) := by
                      apply memoryRel_bool conf target.be (holThe next.tstamps) next.refs next.space
                        target.store target.memory target.mdomain (locals ++ rest) _ _
                      refine ⟨?_, good, ?_, ?_⟩
                      · simpa [locals, rest] using hmem
                      · intro h; simp [out, h]
                      · intro h; simp [out, h]
                    have updated := stateRel_insertRoot conf l1 l2 next target locs dest
                      (DataSem.boolValue answer) (.word out) nextRel (by
                        simpa [locals, rest] using boolRoot)
                    have compiled : compileAssign (width := width) conf n l dest
                        (.blockOp (.boolTest test)) [arg1, arg2] none =
                        assignBoolTest l dest test arg1 arg2 := by rfl
                    refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word out) target, ?_, ?_, ?_⟩
                    · rw [compiled]
                      change WordSemStateFiniteExact.evaluate
                        (setBool (adjustVar dest) .equal (adjustVar arg1) (.reg (adjustVar arg2))) target = _
                      simp [setBool, WordSemStateFiniteExact.evaluate,
                        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVarImm,
                        wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, hw1, hw2]
                      rw [boolSame]
                      cases h : answer <;> simp [out, h]
                    · simp
                    · simpa [next, answer] using updated

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
