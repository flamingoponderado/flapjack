import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux
import Flapjack.Misc.Sptree.Map

/-! Byte-array observation simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- Reading a byte returns the same numeric value under related stores, with
the same type and index checks. This factored case is untagged pending review
of the complete primitive theorem. -/
theorem doApp_derefByte {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp .derefByte) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.memOp .derefByte) args target = .val (value, targetNext) ∧
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
        cases a with
        | number n => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | block ts tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | refPtr bit ptr =>
          cases b with
          | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
          | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
          | refPtr bit p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
          | block ts tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
          | number index =>
            have refs : source.refs.lookup ptr = (sptLookup ptr target.refs).map dataToBviRef := by
              rw [← sptLookup_sptMap]
              exact related.2.2.2.2.1 ptr
            cases found : sptLookup ptr target.refs with
            | none => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, refs, found] at run
            | some entry =>
              cases entry with
              | valueArray values => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, refs, found] at run
              | thunk mode body => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, refs, found] at run
              | mutBlock tag done left child right => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, refs, found] at run
              | byteArray flag bytes =>
                by_cases negative : index < 0
                · simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
                    BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, refs, found, negative] at run
                · cases slot : bytes[index.toNat]? with
                  | none => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
                      BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, refs, found, negative, slot] at run
                  | some byte =>
                    simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
                      BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl, refs, found, negative, slot] at run
                    rcases run with ⟨rfl, rfl⟩
                    refine ⟨target, .number byte.toNat, ?_, ?_, related⟩
                    · simp [DataSem.doAppAux, DataSem.applyNonFfi, found, negative, slot]
                    · simp [dataToBviValue]

/-- Byte-array length observes the same bytes in related stores. This
factored case is untagged pending review of the complete primitive theorem. -/
theorem doApp_lengthByte {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp .lengthByte) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.memOp .lengthByte) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons arg rest =>
    cases rest with
    | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | nil =>
      cases arg with
      | number n => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | block ts tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | refPtr bit ptr =>
        have refs : source.refs.lookup ptr = (sptLookup ptr target.refs).map dataToBviRef := by
          rw [← sptLookup_sptMap]
          exact related.2.2.2.2.1 ptr
        cases found : sptLookup ptr target.refs with
        | none => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, refs, found] at run
        | some entry =>
          cases entry with
          | valueArray values => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, refs, found] at run
          | thunk mode body => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, refs, found] at run
          | mutBlock tag done left child right => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, refs, found] at run
          | byteArray flag bytes =>
            simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
              BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl, refs, found] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨target, .number bytes.length, ?_, ?_, related⟩
            · simp [DataSem.doAppAux, DataSem.applyNonFfi, found]
            · simp [dataToBviValue]

/-- Value-array length is unchanged by element projection. This factored case
is untagged pending review of the complete primitive theorem. -/
theorem doApp_length {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp .length) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.memOp .length) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons arg rest =>
    cases rest with
    | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | nil =>
      cases arg with
      | number n => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | block ts tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | refPtr bit ptr =>
        have refs : source.refs.lookup ptr = (sptLookup ptr target.refs).map dataToBviRef := by
          rw [← sptLookup_sptMap]
          exact related.2.2.2.2.1 ptr
        cases found : sptLookup ptr target.refs with
        | none => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, refs, found] at run
        | some entry =>
          cases entry with
          | byteArray flag bytes => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, refs, found] at run
          | thunk mode body => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, refs, found] at run
          | mutBlock tag done left child right => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, refs, found] at run
          | valueArray values =>
            simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
              BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl, refs, found] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨target, .number values.length, ?_, ?_, related⟩
            · simp [DataSem.doAppAux, DataSem.applyNonFfi, found]
            · simp [dataToBviValue]

end
end Flapjack.Compiler.Backend.BviToData
