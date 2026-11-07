import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux

/-! GC-configuration primitive simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- GC configuration returns unit on two numeric inputs and preserves the
state relation. This factored case is untagged pending review of the complete
primitive theorem. -/
theorem doApp_configGC {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp .configGC) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.memOp .configGC) args target = .val (value, targetNext) ∧
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
        cases a <;> cases b <;> simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback,
          BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.fromBvl_toBvl] at run
        case number.number x y =>
          rcases run with ⟨rfl, rfl⟩
          refine ⟨target, DataSem.unitValue, ?_, dataToBviValue_unit.symm, related⟩
          simp [DataSem.doAppAux, DataSem.applyNonFfi]

end
end Flapjack.Compiler.Backend.BviToData
