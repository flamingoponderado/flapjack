import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux

/-! Block extension simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- Extending a block checks the same bounds and projects the same slices,
while data-side allocation updates timestamps and limits. This factored case
is untagged pending review of the complete primitive theorem. -/
theorem doApp_consExtend {C F : Type} (tag : Nat) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp (.consExtend tag)) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.blockOp (.consExtend tag)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | cons b rest =>
      cases rest with
      | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
      | cons c rest =>
        cases rest with
        | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | cons d tail =>
          cases a <;> try (simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run)
          case block ts oldTag fields =>
            cases b <;> try (simp [dataToBviValue] at run)
            case number lower =>
              cases c <;> try (simp [dataToBviValue] at run)
              case number len =>
                cases d <;> try (simp [dataToBviValue] at run)
                case number total =>
                  by_cases bad : lower < 0 ∨ len < 0 ∨ (↑fields.length : Int) < lower + len ∨
                      total = 0 ∨ total ≠ (↑tail.length : Int) + len
                  · simp [bad] at run
                  · simp [BviSem.fromBvl_toBvl, bad] at run
                    rcases run with ⟨rfl, rfl⟩
                    cases stamps : target.tstamps with
                    | none =>
                      refine ⟨DataSem.checkLim target (tail ++ (fields.drop lower.toNat).take len.toNat).length,
                        .block 0 tag (tail ++ (fields.drop lower.toNat).take len.toNat), ?_, ?_, ?_⟩
                      · simp [DataSem.doAppAux, DataSem.applyNonFfi, DataSem.withFreshTimestamp, bad, stamps]
                      · simp [dataToBviValue, List.map_append, List.map_drop, List.map_take]
                      · simpa [DataSem.checkLim, stateRel] using related
                    | some timestamp =>
                      refine ⟨DataSem.checkLim { target with tstamps := some (timestamp + 1) }
                        (tail ++ (fields.drop lower.toNat).take len.toNat).length,
                        .block timestamp tag (tail ++ (fields.drop lower.toNat).take len.toNat), ?_, ?_, ?_⟩
                      · simp [DataSem.doAppAux, DataSem.applyNonFfi, DataSem.withFreshTimestamp, bad, stamps]
                      · simp [dataToBviValue, List.map_append, List.map_drop, List.map_take]
                      · simpa [DataSem.checkLim, stateRel] using related

end
end Flapjack.Compiler.Backend.BviToData
