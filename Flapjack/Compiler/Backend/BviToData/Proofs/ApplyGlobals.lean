import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux

/-! Global pointer primitive simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- Reading the global pointer preserves the related states. This factored
case is untagged pending review of the complete primitive theorem. -/
theorem doApp_globalsPtr {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.globOp .globalsPtr) (args.map dataToBviValue) source =
      .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.globOp .globalsPtr) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | nil =>
    cases ptr : source.global with
    | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, ptr] at run
    | some n =>
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, ptr] at run
      rcases run with ⟨rfl, rfl⟩
      have targetPtr : target.global = some n := by rw [← related.2.2.2.2.2.2]; exact ptr
      refine ⟨target, .refPtr true n, ?_, ?_, related⟩
      · simp [DataSem.doAppAux, DataSem.applyNonFfi, targetPtr]
      · simp [dataToBviValue]

/-- Updating the global pointer preserves the related states. This factored
case is untagged pending review of the complete primitive theorem. -/
theorem doApp_setGlobalsPtr {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.globOp .setGlobalsPtr) (args.map dataToBviValue) source =
      .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.globOp .setGlobalsPtr) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | cons arg rest =>
    cases rest with
    | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
    | nil =>
      cases arg with
      | number n => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | codePtr n => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | block ts tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | refPtr bit ptr =>
        cases bit with
        | false => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
        | true =>
          simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨{ target with global := some ptr }, DataSem.unitValue, ?_, ?_, ?_⟩
          · simp [DataSem.doAppAux, DataSem.applyNonFfi]
          · exact dataToBviValue_unit.symm
          · rcases related with ⟨clock, code, oracle, compiler, refs, ffi, _⟩
            exact ⟨clock, code, oracle, compiler, refs, ffi, rfl⟩

end
end Flapjack.Compiler.Backend.BviToData
