module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Const
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange

@[expose] public section

/-! The globals-pointer case of the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps

namespace assignGlobalsPtr_correctMap
/-- Canonical target-state roundtrip for the assignment simulation. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end assignGlobalsPtr_correctMap

/-- The original assignment correctness goal for this operation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_GlobalsPtr"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignGlobalsPtr_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet) (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (result : Flapjack.Compiler.Backend.DataSem.Value)
    (globalOp : op = .globOp .globalsPtr)
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
  subst op
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    cases values with
    | cons head tail =>
      simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi] at run
    | nil =>
      cases globalEq : source.global with
      | none =>
        simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq] at run
      | some ptr =>
        simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq] at run
        obtain ⟨rfl, rfl⟩ := run
        let next := DataSem.doStack (.globOp .globalsPtr) []
          (DataSem.doLimSafe source (.globOp .globalsPtr) [])
        have nextRel : stateRel conf l1 l2 next target none locs :=
          stateRel_doStack conf l1 l2 _ target locs _ _
            (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
        have root : memoryRel conf target.be (holThe next.tstamps) next.refs next.space
            target.store target.memory target.mdomain
            ((.refPtr true ptr, holFapply target.store .globals) ::
              joinEnv next.locals (sptToAList (sptInter target.locals (adjustSet next.locals))) ++
              [(theGlobal next.global, holFapply target.store .globals)] ++ flatStack next.stack target.stack) := by
          have hmem := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
          apply memoryRel_rearrange conf target.be (holThe next.tstamps) next.refs next.space
            target.store target.memory target.mdomain _ _ ?_ hmem
          intro pair member
          change pair ∈ (.refPtr true ptr, holFapply target.store .globals) ::
            (joinEnv next.locals (sptToAList (sptInter target.locals (adjustSet next.locals))) ++
              [(theGlobal next.global, holFapply target.store .globals)] ++ flatStack next.stack target.stack) at member
          rcases List.mem_cons.mp member with rfl | member
          · simp [next, DataSem.doStack, DataSem.doLimSafe, globalEq, theGlobal]
          · exact member
        have updated := stateRel_insertRoot conf l1 l2 next target locs dest
          (.refPtr true ptr) (holFapply target.store .globals) nextRel root
        have globalPresent : (target.store.lookup .globals).isSome := nextRel.2.2.2.2.2.2.2.2.2.1 .globals (by simp)
        cases storeEq : target.store.lookup .globals with
        | none => simp [storeEq] at globalPresent
        | some word =>
          have wordEq : holFapply target.store .globals = word := holFapply_of_lookup storeEq
          have compiled : compileAssign (width := width) conf n l dest (.globOp .globalsPtr) args none =
              (.assign (adjustVar dest) (.lookup .globals), l) := by rfl
          refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) word target, ?_, ?_, ?_⟩
          · simp [compiled, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
              WordSemStateFiniteExact.getStore, storeEq]
          · simp
          · simpa [next, DataSem.doStack, DataSem.doLimSafe, globalEq, wordEq] using updated

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
