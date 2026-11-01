import Flapjack.Compiler.Backend.BviToData.Proofs.Build
import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux

/-! List primitive simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendCommon
open Classical
noncomputable section

/-- List append preserves decoded elements and the state relation while the
data semantics assigns fresh timestamps. This factored case is untagged
pending review of the complete primitive theorem. -/
theorem doApp_listAppend {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp .listAppend) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.blockOp .listAppend) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | cons b rest =>
      cases rest with
      | cons c rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
      | nil =>
        have pa := (dataToBviValue_valueToList a).symm
        have pb := (dataToBviValue_valueToList b).symm
        cases ha : DataSem.valueToList a with
        | none =>
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, pa, ha] at run
        | some xs =>
          cases hb : DataSem.valueToList b with
          | none =>
            simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, pa, pb, ha, hb] at run
          | some ys =>
            simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
              BviSem.fromBvl_toBvl, pa, pb, ha, hb] at run
            rcases run with ⟨rfl, rfl⟩
            cases stamps : target.tstamps with
            | none =>
              refine ⟨DataSem.checkLim target 2, DataSem.listToValue 0 b xs, ?_, ?_, ?_⟩
              · simp [DataSem.doAppAux, DataSem.applyNonFfi, DataSem.withFreshTimestamp, ha, hb, stamps]
              · rw [dataToBviValue_listToValue_append xs ys b 0 hb, dataToBviValue_listToValue_nil]
                simp [List.map_append]
              · simpa [DataSem.checkLim, stateRel] using related
            | some ts =>
              refine ⟨DataSem.checkLim { target with tstamps := some (ts + xs.length) } 2,
                DataSem.listToValue ts b xs, ?_, ?_, ?_⟩
              · simp [DataSem.doAppAux, DataSem.applyNonFfi, DataSem.withFreshTimestamp, ha, hb, stamps]
              · rw [dataToBviValue_listToValue_append xs ys b ts hb, dataToBviValue_listToValue_nil]
                simp [List.map_append]
              · simpa [DataSem.checkLim, stateRel] using related

end
end Flapjack.Compiler.Backend.BviToData
