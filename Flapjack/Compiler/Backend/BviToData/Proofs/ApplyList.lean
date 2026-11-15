module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Build
public import Flapjack.Compiler.Backend.BviToData.Proofs.State
public import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux

@[expose] public section

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
        have pa := dataToBviValue_valueToList a
        have pb := dataToBviValue_valueToList b
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

/-- List-to-block conversion checks the requested length and preserves every
decoded element while data timestamps and limits are updated. This factored
case is untagged pending review of the complete primitive theorem. -/
theorem doApp_fromList {C F : Type} (tag : Nat) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp (.fromList tag)) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.blockOp (.fromList tag)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | cons length rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
    | cons list rest =>
      cases rest with
      | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | nil =>
        have projected := dataToBviValue_valueToList list
        cases decoded : DataSem.valueToList list with
        | none =>
          cases length <;> simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback,
            BviSem.doAppAux, projected, decoded] at run
        | some values =>
          cases length with
          | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, projected, decoded] at run
          | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, projected, decoded] at run
          | refPtr bit p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, projected, decoded] at run
          | block ts t vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, projected, decoded] at run
          | number n =>
            by_cases valid : n = Int.ofNat values.length
            · simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, projected, decoded, valid] at run
              rcases run with ⟨rfl, rfl⟩
              cases values with
              | nil =>
                refine ⟨target, .block 0 tag [], ?_, ?_, related⟩
                · simp [DataSem.doAppAux, DataSem.applyNonFfi, decoded, valid]
                · simp [dataToBviValue]
              | cons first rest =>
                cases stamps : target.tstamps with
                | none =>
                  refine ⟨DataSem.checkLim target (first :: rest).length, .block 0 tag (first :: rest), ?_, ?_, ?_⟩
                  · simp [DataSem.doAppAux, DataSem.applyNonFfi, DataSem.withFreshTimestamp, decoded, valid, stamps]
                  · simp [dataToBviValue]
                  · simpa [DataSem.checkLim, stateRel] using related
                | some ts =>
                  refine ⟨DataSem.checkLim { target with tstamps := some (ts + 1) } (first :: rest).length,
                    .block ts tag (first :: rest), ?_, ?_, ?_⟩
                  · simp [DataSem.doAppAux, DataSem.applyNonFfi, DataSem.withFreshTimestamp, decoded, valid, stamps]
                  · simp [dataToBviValue]
                  · simpa [DataSem.checkLim, stateRel] using related
            · have invalid : n ≠ (↑values.length : Int) := valid
              simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, projected, decoded, invalid] at run

/-- Ordinary block construction preserves its tag and all fields, with the
data-side timestamp and limit bookkeeping hidden by the state relation. This
factored case is untagged pending review of the complete primitive theorem. -/
theorem doApp_cons {C F : Type} (tag : Nat) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp (.cons tag)) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.blockOp (.cons tag)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
    BviSem.fromBvl_toBvl] at run
  rcases run with ⟨rfl, rfl⟩
  cases args with
  | nil =>
    refine ⟨target, .block 0 tag [], ?_, ?_, related⟩
    · simp [DataSem.doAppAux, DataSem.applyNonFfi]
    · simp [dataToBviValue]
  | cons first rest =>
    cases stamps : target.tstamps with
    | none =>
      refine ⟨DataSem.checkLim target (first :: rest).length, .block 0 tag (first :: rest), ?_, ?_, ?_⟩
      · simp [DataSem.doAppAux, DataSem.applyNonFfi, DataSem.withFreshTimestamp, stamps]
      · simp [dataToBviValue]
      · simpa [DataSem.checkLim, stateRel] using related
    | some ts =>
      refine ⟨DataSem.checkLim { target with tstamps := some (ts + 1) } (first :: rest).length,
        .block ts tag (first :: rest), ?_, ?_, ?_⟩
      · simp [DataSem.doAppAux, DataSem.applyNonFfi, DataSem.withFreshTimestamp, stamps]
      · simp [dataToBviValue]
      · simpa [DataSem.checkLim, stateRel] using related

end
end Flapjack.Compiler.Backend.BviToData
