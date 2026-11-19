module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.FfiSetup

@[expose] public section

/-! FFI assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.BackendProps

namespace assignFfiCorrectMap
/-- Canonical target-state roundtrip for the assignment simulation. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end assignFfiCorrectMap

/-- Foreign-call assignment satisfies the complete original assignment goal.
The evaluator inherits the real-model assumption in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_FFI"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignFfi_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (result : Flapjack.Compiler.Backend.DataSem.Value)
    (ffiOp : ∃ name, op = .ffi name)
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
  obtain ⟨name, rfl⟩ := ffiOp
  cases names with
  | none => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | some names =>
    obtain ⟨firstVar, secondVar, config, bytes, address1, wordCut, ffi, address2, updated,
      argsShape, setupRun, callRun, resultEq, postRel, execution⟩ :=
      ffi_success_postState conf l1 l2 source cut resultState target locs names args values name result
        related cutEq argsEq run
    by_cases shortcut : (!conf.callEmptyFfi && name == Basis.Pure.MlString.ofString "") = true
    · have nameEq : name = Basis.Pure.MlString.ofString "" := by
        have condition := shortcut
        simp at condition
        exact condition.2
      obtain ⟨base, flag1, flag2, first, second, config, bytes, updated, ffi,
        baseRun, valuesShape, firstRead, secondRead, ffiRun, lengthEq, unitEq, resultStateEq⟩ :=
        doApp_ffi_success name values cut resultState result run
      have identity : ffi = cut.ffi ∧ updated = bytes := by
        rw [nameEq] at ffiRun
        simpa [Basis.Pure.MlString.ofString, callFFIHOL_empty_extCall] using ffiRun.symm
      have baseRefs : base.refs = cut.refs := by
        simp [DataSem.doSpace, DataLang.opSpaceReset] at baseRun
        subst base
        rfl
      have baseFfi : base.ffi = cut.ffi := by
        simp [DataSem.doSpace, DataLang.opSpaceReset] at baseRun
        subst base
        rfl
      let prepared := DataSem.doStack (.ffi name) values (DataSem.doLimSafe base (.ffi name) values)
      have preparedRefs : prepared.refs = cut.refs := by
        simpa [prepared, DataSem.doStack, DataSem.doLimSafe] using baseRefs
      have preparedFfi : prepared.ffi = cut.ffi := by
        simpa [prepared, DataSem.doStack, DataSem.doLimSafe] using baseFfi
      have sourceEq : resultState = prepared := by
        rw [resultStateEq, identity.2, sptInsertUnchanged cut.refs second (.byteArray false bytes) secondRead,
          identity.1, ← preparedRefs, ← preparedFfi]
      have cutRel := stateRel_cutOpt conf l1 l2 source target locs (some names) cut ⟨related, cutEq⟩
      obtain ⟨base', baseRun', baseRel⟩ := stateRel_doSpace_ffi conf l1 l2 cut target locs name values cutRel
      have baseEq : base = base' := Option.some.inj (baseRun.symm.trans baseRun')
      subst base'
      have limRel := stateRel_doLimSafe conf l1 l2 base target locs (.ffi name) values baseRel
      have stackRel := stateRel_doStack conf l1 l2 (DataSem.doLimSafe base (.ffi name) values)
        target locs (.ffi name) values limRel
      have postRel : stateRel conf l1 l2 resultState target none locs := by
        rw [sourceEq]
        exact stackRel
      have good := postRel.2.2.2.2.2.2.1
      have memory := postRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have unitRoot := Memory.memoryRel_unit conf target.be (holThe resultState.tstamps) resultState.refs
        resultState.space target.store target.memory target.mdomain _ ⟨memory, good⟩
      have finalRel := stateRel_insertRoot conf l1 l2 resultState target locs dest DataSem.unitValue (.word 2)
        postRel (by simpa using unitRoot)
      refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) target, ?_, ?_, ?_⟩
      · simp [compileAssign, arg2, assignFfi, argsShape, shortcut,
          WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
      · simp
      · simpa [unitEq] using finalRel
    · obtain ⟨fullRun, finalRel⟩ := execution dest
      let post := { target with locals := wordCut, fpRegs := HolFiniteMapExact.empty, ffi := ffi, memory := (if name == Basis.Pure.MlString.ofString "" then target.memory else writeBytearrayExact (address2 + wordSemBytesInWord) updated target.memory target.mdomain target.be) }
      refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) post, ?_, ?_, ?_⟩
      · by_cases emptyName : name = Basis.Pure.MlString.ofString ""
        · have enabled : conf.callEmptyFfi = true := by
            cases h : conf.callEmptyFfi <;> simp [emptyName, h] at shortcut ⊢
          simpa [compileAssign, arg2, assignFfi, argsShape, post, emptyName, enabled] using fullRun
        · simpa [compileAssign, arg2, assignFfi, argsShape, post, emptyName] using fullRun
      · simp
      · by_cases emptyName : name = Basis.Pure.MlString.ofString "" <;>
          simpa [post, emptyName] using finalRel

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
