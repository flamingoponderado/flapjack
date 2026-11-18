module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Const
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.CodePointer

@[expose] public section

/-! Code-label assignment in the data-to-word simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps

namespace assignLabelMap
/-- Canonical target-state roundtrip for the assignment simulation. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end assignLabelMap

/-- A source label assignment satisfies the full assignment goal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_Label"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignLabel_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (result : Flapjack.Compiler.Backend.DataSem.Value)
    (labelOp : ∃ lab, op = .label lab)
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (_argsEq : DataSem.getVars args source.locals = some values)
    (_depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r,
      WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q, r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace →
        stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  obtain ⟨lab, rfl⟩ := labelOp
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    cases values with
    | cons v vs => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi] at run
    | nil =>
      cases codeEq : sptLookup lab source.code with
      | none => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, codeEq] at run
      | some entry =>
        simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, codeEq] at run
        obtain ⟨rfl, rfl⟩ := run
        let next := DataSem.doStack (.label lab) [] (DataSem.doLimSafe source (.label lab) [])
        have nextRel : stateRel conf l1 l2 next target none locs :=
          stateRel_doStack conf l1 l2 _ target locs _ _
            (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
        have codeRel := related.2.2.2.2.1
        obtain ⟨arity, body⟩ := entry
        have targetCode := codeRel.2.2 lab arity body codeEq
        have targetMem : sptMem lab target.code := by
          apply (sptMem_iff_lookup _ _).2
          exact ⟨_, targetCode⟩
        have root := memoryRel_codePtr conf target.be (holThe next.tstamps) next.refs next.space
          target.store target.memory target.mdomain lab
          (joinEnv next.locals (sptToAList (sptInter target.locals (adjustSet next.locals))) ++
            [(theGlobal next.global, holFapply target.store .globals)] ++ flatStack next.stack target.stack)
          (by simpa using nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
        have updated := stateRel_insertRoot conf l1 l2 next target locs dest (.codePtr lab)
          (.loc lab 0) nextRel root
        have compiled : compileAssign (width := width) conf n l dest (.label lab) args none =
            (.locValue (adjustVar dest) lab, l) := by rfl
        refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) (.loc lab 0) target, ?_, ?_, ?_⟩
        · simp [compiled, WordSemStateFiniteExact.evaluate, targetMem]
        · simp
        · simpa [next, DataSem.doStack, DataSem.doLimSafe] using updated

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
