module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Thunk
public import Flapjack.Compiler.Backend.BviToData.Proofs.Build
public import Flapjack.Compiler.Backend.BviToData.Proofs.State
public import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux
public import Flapjack.Misc.Sptree.Map

@[expose] public section

/-! Thunk primitive simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- Thunk allocation preserves the update restriction, chosen pointer and
reference contents. This factored case is untagged pending review of the
complete primitive theorem. -/
theorem doApp_allocThunk {C F : Type} (mode : AstHOL.ThunkMode) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.thunkOp (.allocThunk mode)) (args.map dataToBviValue) source =
      .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.thunkOp (.allocThunk mode)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
  | cons arg rest =>
    cases rest with
    | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
    | nil =>
      have refs : ∀ n, source.refs.lookup n = (sptLookup n target.refs).map dataToBviRef := by
        intro n
        rw [← sptLookup_sptMap]
        exact related.2.2.2.2.1 n
      have restriction := badThunkUpdate_projection mode arg target.refs source.refs refs
      by_cases bad : DataSem.badThunkUpdate mode arg target.refs
      · have sourceBad := restriction.mpr bad
        simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
          BviSem.toBvl, sourceBad] at run
      · have sourceGood : ¬ BvlSem.badThunkUpdate mode (dataToBviValue arg) source.refs :=
          fun h => bad (restriction.mp h)
        have fresh := leastUnusedRef_projection target.refs source.refs refs
        simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
          BviSem.toBvl, BviSem.fromBvl, sourceGood, fresh] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨{ target with refs := sptInsert (DataSem.leastUnusedRef target.refs) (.thunk mode arg) target.refs },
          .refPtr false (DataSem.leastUnusedRef target.refs), ?_, ?_, ?_⟩
        · simp [DataSem.doAppAux, DataSem.applyNonFfi, bad]
        · simp [dataToBviValue]
        · simpa [dataToBviRef] using stateRel_insertRef source target related
            (DataSem.leastUnusedRef target.refs) (.thunk mode arg)

/-- Updating an unevaluated thunk preserves the update guard and all store
lookups. This factored case is untagged pending review of the complete
primitive theorem. -/
theorem doApp_updateThunk {C F : Type} (mode : AstHOL.ThunkMode) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.thunkOp (.updateThunk mode)) (args.map dataToBviValue) source =
      .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.thunkOp (.updateThunk mode)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
  | cons pointer rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
    | cons arg rest =>
      cases rest with
      | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
      | nil =>
        cases pointer with
        | number n => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | block ts tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | refPtr bit ptr =>
          cases bit with
          | true => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
          | false =>
            have refs : ∀ n, source.refs.lookup n = (sptLookup n target.refs).map dataToBviRef := by
              intro n
              rw [← sptLookup_sptMap]
              exact related.2.2.2.2.1 n
            have restriction := badThunkUpdate_projection mode arg target.refs source.refs refs
            by_cases bad : DataSem.badThunkUpdate mode arg target.refs
            · have sourceBad := restriction.mpr bad
              simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
                BvlSem.doApp, BviSem.toBvl, sourceBad] at run
            · have sourceGood : ¬ BvlSem.badThunkUpdate mode (dataToBviValue arg) source.refs :=
                fun h => bad (restriction.mp h)
              cases found : sptLookup ptr target.refs with
              | none =>
                simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
                  BvlSem.doApp, BviSem.toBvl, sourceGood, refs, found] at run
              | some entry =>
                cases entry with
                | valueArray vs =>
                  simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
                    BvlSem.doApp, BviSem.toBvl, sourceGood, refs, found] at run
                | byteArray flag bytes =>
                  simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
                    BvlSem.doApp, BviSem.toBvl, sourceGood, refs, found] at run
                | mutBlock tag done left child right =>
                  simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
                    BvlSem.doApp, BviSem.toBvl, sourceGood, refs, found] at run
                | thunk oldMode oldValue =>
                  cases oldMode with
                  | evaluated =>
                    simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
                      BvlSem.doApp, BviSem.toBvl, sourceGood, refs, found] at run
                  | notEvaluated =>
                    simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
                      BvlSem.doApp, BviSem.toBvl, BviSem.fromBvl, sourceGood, refs, found] at run
                    rcases run with ⟨rfl, rfl⟩
                    refine ⟨{ target with refs := sptInsert ptr (.thunk mode arg) target.refs },
                      DataSem.unitValue, ?_, dataToBviValue_unit.symm, ?_⟩
                    · simp [DataSem.doAppAux, DataSem.applyNonFfi, bad, found]
                    · simpa [dataToBviRef] using stateRel_insertRef source target related ptr (.thunk mode arg)

end
end Flapjack.Compiler.Backend.BviToData
