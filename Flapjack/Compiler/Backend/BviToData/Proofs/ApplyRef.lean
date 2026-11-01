import Flapjack.Compiler.Backend.BviToData.Proofs.Build
import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux
import Flapjack.Misc.Sptree.Map

/-! Reference allocation simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- Allocating a reference array selects the same fresh pointer and inserts
corresponding values into the two stores. This factored case is untagged
pending review of the complete primitive theorem. -/
theorem doApp_ref {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp .ref) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.memOp .ref) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  have refs : ∀ n, source.refs.lookup n = (sptLookup n target.refs).map dataToBviRef := by
    intro n
    rw [← sptLookup_sptMap]
    exact related.2.2.2.2.1 n
  have fresh := leastUnusedRef_projection target.refs source.refs refs
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
    BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl, fresh] at run
  rcases run with ⟨rfl, rfl⟩
  refine ⟨{ target with refs := sptInsert (DataSem.leastUnusedRef target.refs) (.valueArray args) target.refs },
    .refPtr true (DataSem.leastUnusedRef target.refs), ?_, ?_, ?_⟩
  · simp [DataSem.doAppAux, DataSem.applyNonFfi]
  · simp [dataToBviValue]
  · simpa [dataToBviRef] using
      stateRel_insertRef source target related (DataSem.leastUnusedRef target.refs) (.valueArray args)

/-- Replicated-array allocation agrees for all argument lists, including
negative lengths and malformed inputs. This factored case is untagged pending
review of the complete primitive theorem. -/
theorem doApp_refArray {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp .refArray) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.memOp .refArray) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons count rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons value rest =>
      cases rest with
      | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | nil =>
        cases count with
        | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | refPtr b p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | block t tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | number count =>
          by_cases negative : count < 0
          · simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
              BvlSem.doApp, BvlSem.applyMemory, negative] at run
          · have refs : ∀ n, source.refs.lookup n = (sptLookup n target.refs).map dataToBviRef := by
              intro n
              rw [← sptLookup_sptMap]
              exact related.2.2.2.2.1 n
            have fresh := leastUnusedRef_projection target.refs source.refs refs
            simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
              BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl, negative, fresh] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨{ target with refs := sptInsert (DataSem.leastUnusedRef target.refs) (.valueArray (List.replicate count.toNat value)) target.refs },
              .refPtr true (DataSem.leastUnusedRef target.refs), ?_, ?_, ?_⟩
            · simp [DataSem.doAppAux, DataSem.applyNonFfi, negative]
            · simp [dataToBviValue]
            · simpa [dataToBviRef] using stateRel_insertRef source target related
                (DataSem.leastUnusedRef target.refs) (.valueArray (List.replicate count.toNat value))

/-- Byte-array allocation preserves the fresh address and byte contents.
This factored case is untagged pending review of the complete primitive theorem. -/
theorem doApp_refByte {C F : Type} (flag : Bool) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp (.refByte flag)) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.memOp (.refByte flag)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | cons count rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
    | cons byte rest =>
      cases rest with
      | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | nil =>
        cases count with
        | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
        | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
        | refPtr b p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
        | block t tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
        | number count =>
          cases byte with
          | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
          | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
          | refPtr b p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
          | block t tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
          | number byte =>
            by_cases negative : count < 0
            · simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, negative] at run
            · cases decoded : ClosSem.intToByte byte with
              | none => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, negative, decoded] at run
              | some b =>
                have refs : ∀ n, source.refs.lookup n = (sptLookup n target.refs).map dataToBviRef := by
                  intro n
                  rw [← sptLookup_sptMap]
                  exact related.2.2.2.2.1 n
                have fresh := leastUnusedRef_projection target.refs source.refs refs
                simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
                  negative, decoded, fresh] at run
                rcases run with ⟨rfl, rfl⟩
                refine ⟨{ target with refs := sptInsert (DataSem.leastUnusedRef target.refs) (.byteArray flag (List.replicate count.toNat b)) target.refs },
                  .refPtr true (DataSem.leastUnusedRef target.refs), ?_, ?_, ?_⟩
                · simp [DataSem.doAppAux, DataSem.applyNonFfi, negative, decoded]
                · simp [dataToBviValue]
                · simpa [dataToBviRef] using stateRel_insertRef source target related
                    (DataSem.leastUnusedRef target.refs) (.byteArray flag (List.replicate count.toNat b))

end
end Flapjack.Compiler.Backend.BviToData
