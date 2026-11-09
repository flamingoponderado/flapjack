module

public import Flapjack.Compiler.Backend.BviToData.Proofs.State
public import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux
public import Flapjack.Misc.Sptree.Map

@[expose] public section

/-! Array bounds-check simulations for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- Byte-array bounds checks preserve strict and inclusive modes. This
factored case is untagged pending review of the complete primitive theorem. -/
theorem doApp_boundsCheckByte {C F : Type} (loose : Bool) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp (.boundsCheckByte loose)) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value, DataSem.doAppAux (.memOp (.boundsCheckByte loose)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons b rest =>
      cases rest with
      | cons c rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | nil =>
        cases a <;> try (simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run)
        case refPtr bit ptr =>
          cases b <;> try (simp [dataToBviValue] at run)
          case number index =>
            have refs : source.refs.lookup ptr = (sptLookup ptr target.refs).map dataToBviRef := by
              rw [← sptLookup_sptMap]
              exact related.2.2.2.2.1 ptr
            cases found : sptLookup ptr target.refs with
            | none => simp [BviSem.toBvl, refs, found] at run
            | some entry =>
              cases entry with
              | valueArray values => simp [dataToBviRef, BviSem.toBvl, refs, found] at run
              | thunk mode body => simp [dataToBviRef, BviSem.toBvl, refs, found] at run
              | mutBlock tag done left child right => simp [dataToBviRef, BviSem.toBvl, refs, found] at run
              | byteArray flag bytes =>
                simp [dataToBviRef, BviSem.toBvl, BviSem.fromBvl, refs, found] at run
                rcases run with ⟨rfl, rfl⟩
                refine ⟨target, DataSem.boolValue (decide (0 ≤ index ∧ if loose then index ≤ Int.ofNat bytes.length else index < Int.ofNat bytes.length)),
                  ?_, ?_, related⟩
                · simp [DataSem.doAppAux, DataSem.applyNonFfi, found]
                · cases loose <;> simp [dataToBviValue_bool]

/-- Value-array bounds checks preserve the indexed array's length. This
factored case is untagged pending review of the complete primitive theorem. -/
theorem doApp_boundsCheckArray {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp .boundsCheckArray) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value, DataSem.doAppAux (.memOp .boundsCheckArray) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons b rest =>
      cases rest with
      | cons c rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | nil =>
        cases a <;> try (simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run)
        case refPtr bit ptr =>
          cases b <;> try (simp [dataToBviValue] at run)
          case number index =>
            have refs : source.refs.lookup ptr = (sptLookup ptr target.refs).map dataToBviRef := by
              rw [← sptLookup_sptMap]
              exact related.2.2.2.2.1 ptr
            cases found : sptLookup ptr target.refs with
            | none => simp [BviSem.toBvl, refs, found] at run
            | some entry =>
              cases entry with
              | byteArray flag bytes => simp [dataToBviRef, BviSem.toBvl, refs, found] at run
              | thunk mode body => simp [dataToBviRef, BviSem.toBvl, refs, found] at run
              | mutBlock tag done left child right => simp [dataToBviRef, BviSem.toBvl, refs, found] at run
              | valueArray values =>
                simp [dataToBviRef, BviSem.toBvl, BviSem.fromBvl, refs, found] at run
                rcases run with ⟨rfl, rfl⟩
                refine ⟨target, DataSem.boolValue (decide (0 ≤ index ∧ index < Int.ofNat values.length)),
                  ?_, ?_, related⟩
                · simp [DataSem.doAppAux, DataSem.applyNonFfi, found]
                · simp [dataToBviValue_bool]

end
end Flapjack.Compiler.Backend.BviToData
