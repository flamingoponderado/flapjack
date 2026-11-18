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

/-- The globals-pointer assignment case, retaining all premises and result
branches of the HOL assignment goal. Its compiler and state relation are
pending source review, so this theorem does not yet carry a HOL reference. -/
theorem assignGlobalsPtr_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (n l l1 l2 dest : Nat) (op : ClosLang.Op)
    (args : List Nat) (names : Option NumSet) (source cut resultState : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List DataSem.Value) (result : DataSem.Value)
    (globalOp : op = .globOp .globalsPtr)
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (_argsEq : DataSem.getVars args source.locals = some values)
    (_depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r,
      WordSemStateFiniteExact.evaluate (compileControl conf n l (.assign dest op args names)).1 target = (q, r) ∧
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
          have compiled : compileControl (width := width) conf n l (.assign dest (.globOp .globalsPtr) args none) =
              (.assign (adjustVar dest) (.lookup .globals), l) := by
            have h := compileControl_option (width := width) conf n l (.assign dest (.globOp .globalsPtr) args none)
            simpa [compileControl?, compileAssign] using h.symm
          refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) word target, ?_, ?_, ?_⟩
          · simp [compiled, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
              WordSemStateFiniteExact.getStore, storeEq]
          · simp
          · simpa [next, DataSem.doStack, DataSem.doLimSafe, globalEq, wordEq] using updated

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
