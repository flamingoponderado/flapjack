import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux
import Flapjack.Misc.Sptree.Map

/-! Fixed-index read simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- Fixed-index reads return the corresponding field from either a block or
a reference array. This factored case is untagged pending review of the
complete primitive theorem. -/
theorem doApp_elemAt {C F : Type} (index : Nat) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp (.elemAt index)) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.blockOp (.elemAt index)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons arg rest =>
    cases rest with
    | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | nil =>
      cases arg with
      | number n => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
      | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
      | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
      | block ts tag values =>
        cases slot : values[index]? with
        | none => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
            BvlSem.doApp, BvlSem.applyBlock, List.getElem?_map, slot] at run
        | some value =>
          simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
            BvlSem.doApp, BvlSem.applyBlock, BviSem.fromBvl_toBvl, List.getElem?_map, slot] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨target, value, ?_, rfl, related⟩
          simp [DataSem.doAppAux, DataSem.applyNonFfi, slot]
      | refPtr bit ptr =>
        have refs : source.refs.lookup ptr = (sptLookup ptr target.refs).map dataToBviRef := by
          rw [← sptLookup_sptMap]
          exact related.2.2.2.2.1 ptr
        cases found : sptLookup ptr target.refs with
        | none => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
            BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, refs, found] at run
        | some entry =>
          cases entry with
          | byteArray flag bytes => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback,
              BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, refs, found] at run
          | thunk mode body => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback,
              BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, refs, found] at run
          | mutBlock tag done left child right => simp [dataToBviValue, dataToBviRef, BviSem.doApp,
              BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, refs, found] at run
          | valueArray values =>
            cases slot : values[index]? with
            | none => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
                BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, refs, found, List.getElem?_map, slot] at run
            | some value =>
              simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
                BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, BviSem.fromBvl, refs, found, List.getElem?_map, slot] at run
              rcases run with ⟨rfl, rfl⟩
              refine ⟨target, value, ?_, rfl, related⟩
              simp [DataSem.doAppAux, DataSem.applyNonFfi, found, slot]

private theorem bviEl_eq_elemAt {C F : Type} (index : Int) (arg : BvlSem.Value)
    (state : BviSem.BviState C F) (nonnegative : ¬ index < 0) :
    BviSem.doApp (.memOp .el) [arg, .number index] state =
      BviSem.doApp (.blockOp (.elemAt index.toNat)) [arg] state := by
  cases arg <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
    BvlSem.doApp, BvlSem.applyMemory, BvlSem.applyBlock, nonnegative]
  rfl

private theorem dataEl_eq_elemAt {C F : Type} (index : Int) (arg : DataSem.Value)
    (state : DataSem.State C F) (nonnegative : ¬ index < 0) :
    DataSem.doAppAux (.memOp .el) [arg, .number index] state =
      DataSem.doAppAux (.blockOp (.elemAt index.toNat)) [arg] state := by
  cases arg <;> simp [DataSem.doAppAux, DataSem.applyNonFfi, nonnegative]

/-- A dynamic nonnegative index reduces to the fixed-index read, and negative
indices are rejected. This factored case is untagged pending review of the
complete primitive theorem. -/
theorem doApp_el {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp .el) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.memOp .el) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons arg rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons i rest =>
      cases rest with
      | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | nil =>
        cases i with
        | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | refPtr bit p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | block ts tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | number index =>
          by_cases negative : index < 0
          · cases arg <;> simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
              BvlSem.doApp, BvlSem.applyMemory, negative] at run
            case refPtr bit ptr =>
              cases found : source.refs.lookup ptr with
              | none => simp [BviSem.toBvl, found] at run
              | some entry => cases entry <;> simp [BviSem.toBvl, found] at run
          · have readRun : BviSem.doApp (.blockOp (.elemAt index.toNat)) [dataToBviValue arg] source = .val (result, next) := by
              simpa [dataToBviValue, bviEl_eq_elemAt index (dataToBviValue arg) source negative] using run
            obtain ⟨targetNext, value, dataRun, eq, nextRel⟩ := doApp_elemAt index.toNat [arg] source target related result next readRun
            refine ⟨targetNext, value, ?_, eq, nextRel⟩
            simpa [dataEl_eq_elemAt index arg target negative] using dataRun

end
end Flapjack.Compiler.Backend.BviToData
