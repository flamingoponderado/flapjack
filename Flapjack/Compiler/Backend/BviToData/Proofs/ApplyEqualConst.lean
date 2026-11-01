import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux
import Flapjack.Misc.Sptree.Map

/-! Constant-comparison simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- Constant comparisons preserve integer, word, and immutable-byte-string
results and reject the same malformed references. This factored case is
untagged pending review of the complete primitive theorem. -/
theorem doApp_equalConst {C F : Type} (part : ClosLang.ConstPart) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp (.equalConst part)) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.blockOp (.equalConst part)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => cases part <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons arg rest =>
    cases rest with
    | cons a rest => cases part <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | nil =>
      cases part with
      | con tag indexes => cases arg <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
      | int i =>
        cases arg <;> simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyBlock, BviSem.fromBvl_toBvl] at run
        case number j =>
          rcases run with ⟨rfl, rfl⟩
          refine ⟨target, DataSem.boolValue (decide (i = j)), ?_, (dataToBviValue_bool _).symm, related⟩
          simp [DataSem.doAppAux, DataSem.applyNonFfi]
      | w64 i =>
        cases arg <;> simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyBlock, BviSem.fromBvl_toBvl] at run
        case word64 j =>
          rcases run with ⟨rfl, rfl⟩
          refine ⟨target, DataSem.boolValue (decide (i = j)), ?_, (dataToBviValue_bool _).symm, related⟩
          simp [DataSem.doAppAux, DataSem.applyNonFfi]
      | str text =>
        cases arg with
        | number n => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | block ts tag fields => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | refPtr bit ptr =>
          have refs : source.refs.lookup ptr = (sptLookup ptr target.refs).map dataToBviRef := by
            rw [← sptLookup_sptMap]
            exact related.2.2.2.2.1 ptr
          cases found : sptLookup ptr target.refs with
          | none => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, refs, found] at run
          | some entry =>
            cases entry with
            | valueArray values => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, refs, found] at run
            | thunk mode body => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, refs, found] at run
            | mutBlock tag done left child right => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, refs, found] at run
            | byteArray flag bytes =>
              cases flag with
              | false => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, refs, found] at run
              | true =>
                simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
                  BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, BviSem.fromBvl, refs, found] at run
                rcases run with ⟨rfl, rfl⟩
                refine ⟨target, DataSem.boolValue (decide (bytes = text.explode)), ?_, (dataToBviValue_bool _).symm, related⟩
                simp [DataSem.doAppAux, DataSem.applyNonFfi, found]

end
end Flapjack.Compiler.Backend.BviToData
