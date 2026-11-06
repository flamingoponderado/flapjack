import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux
import Flapjack.Misc.Sptree.Map

/-! Byte-array primitive simulations for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString
open Classical
noncomputable section

/-- String comparison observes the same bytes on both sides and returns the
same Boolean value. This factored case is untagged pending review of the
complete primitive theorem. -/
theorem doApp_stringCmp {C F : Type} (fast : Bool) (cmp : Opb) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp (.stringCmp fast cmp)) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value, DataSem.doAppAux (.memOp (.stringCmp fast cmp)) args target = .val (value, targetNext) ∧
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
          BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl] at run
        case refPtr.refPtr flag leftPtr bit rightPtr =>
          have refs : ∀ key, source.refs.lookup key = (sptLookup key target.refs).map dataToBviRef := by
            intro key
            rw [← sptLookup_sptMap]
            exact related.2.2.2.2.1 key
          cases leftFound : sptLookup leftPtr target.refs with
          | none => simp [refs, leftFound] at run
          | some leftEntry =>
            cases leftEntry with
            | valueArray values => simp [refs, leftFound, dataToBviRef] at run
            | thunk mode body => simp [refs, leftFound, dataToBviRef] at run
            | mutBlock tag done left child right => simp [refs, leftFound, dataToBviRef] at run
            | byteArray leftFlag leftBytes =>
              cases rightFound : sptLookup rightPtr target.refs with
              | none => simp [refs, leftFound, rightFound, dataToBviRef] at run
              | some rightEntry =>
                cases rightEntry with
                | valueArray values => simp [refs, leftFound, rightFound, dataToBviRef] at run
                | thunk mode body => simp [refs, leftFound, rightFound, dataToBviRef] at run
                | mutBlock tag done left child right => simp [refs, leftFound, rightFound, dataToBviRef] at run
                | byteArray rightFlag rightBytes =>
                  simp [refs, leftFound, rightFound, dataToBviRef, BviSem.fromBvl] at run
                  rcases run with ⟨rfl, rfl⟩
                  refine ⟨target, DataSem.boolValue (strCmp fast cmp (.implode leftBytes) (.implode rightBytes)),
                    ?_, (dataToBviValue_bool _).symm, related⟩
                  simp [DataSem.doAppAux, DataSem.applyNonFfi, leftFound, rightFound]

/-- Byte-array XOR observes both input arrays and preserves the relation after
updating the destination. This factored case is untagged pending review of the
complete primitive theorem. -/
theorem doApp_xorByte {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp .xorByte) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value, DataSem.doAppAux (.memOp .xorByte) args target = .val (value, targetNext) ∧
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
          BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl] at run
        case refPtr.refPtr dstBit dst srcBit src =>
          have refs : ∀ key, source.refs.lookup key = (sptLookup key target.refs).map dataToBviRef := by
            intro key
            rw [← sptLookup_sptMap]
            exact related.2.2.2.2.1 key
          cases srcFound : sptLookup src target.refs with
          | none => simp [refs, srcFound] at run
          | some srcEntry =>
            cases srcEntry with
            | valueArray values => simp [refs, srcFound, dataToBviRef] at run
            | thunk mode body => simp [refs, srcFound, dataToBviRef] at run
            | mutBlock tag done left child right => simp [refs, srcFound, dataToBviRef] at run
            | byteArray srcFlag srcBytes =>
              cases dstFound : sptLookup dst target.refs with
              | none => simp [refs, srcFound, dstFound, dataToBviRef] at run
              | some dstEntry =>
                cases dstEntry with
                | valueArray values => simp [refs, srcFound, dstFound, dataToBviRef] at run
                | thunk mode body => simp [refs, srcFound, dstFound, dataToBviRef] at run
                | mutBlock tag done left child right => simp [refs, srcFound, dstFound, dataToBviRef] at run
                | byteArray dstFlag dstBytes =>
                  cases xorRun : xorBytes srcBytes dstBytes with
                  | none => simp [refs, srcFound, dstFound, dataToBviRef, xorRun] at run
                  | some updated =>
                    simp [refs, srcFound, dstFound, dataToBviRef, BviSem.fromBvl, xorRun] at run
                    rcases run with ⟨rfl, rfl⟩
                    refine ⟨{ target with refs := sptInsert dst (.byteArray dstFlag updated) target.refs },
                      DataSem.unitValue, ?_, dataToBviValue_unit.symm, ?_⟩
                    · simp [DataSem.doAppAux, DataSem.applyNonFfi, srcFound, dstFound, xorRun]
                    · simpa [dataToBviRef] using stateRel_insertRef source target related dst (.byteArray dstFlag updated)

/-- Copying bytes between two arrays preserves the reference-store relation,
including when the source and destination refer to the same array. This is an
untagged case of the primitive simulation pending evaluator review. -/
theorem doApp_copyByte_false {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp (.copyByte false)) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value, DataSem.doAppAux (.memOp (.copyByte false)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons b rest =>
      cases rest with
      | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | cons c rest =>
        cases rest with
        | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | cons d rest =>
          cases rest with
          | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
          | cons e rest =>
            cases rest with
            | cons f rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
            | nil =>
              cases a <;> try (simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback,
                BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl] at run)
              case refPtr srcBit src =>
                cases b <;> try (simp [dataToBviValue] at run)
                case number offset =>
                  cases c <;> try (simp [dataToBviValue] at run)
                  case number length =>
                    cases d <;> try (simp [dataToBviValue] at run)
                    case refPtr dstBit dst =>
                      cases e <;> try (simp [dataToBviValue] at run)
                      case number dstOffset =>
                        have refs : ∀ key, source.refs.lookup key = (sptLookup key target.refs).map dataToBviRef := by
                          intro key
                          rw [← sptLookup_sptMap]
                          exact related.2.2.2.2.1 key
                        cases srcFound : sptLookup src target.refs with
                        | none => simp [refs, srcFound] at run
                        | some srcEntry =>
                          cases srcEntry with
                          | valueArray values => simp [refs, srcFound, dataToBviRef] at run
                          | thunk mode body => simp [refs, srcFound, dataToBviRef] at run
                          | mutBlock tag done left child right => simp [refs, srcFound, dataToBviRef] at run
                          | byteArray srcFlag srcBytes =>
                            cases dstFound : sptLookup dst target.refs with
                            | none => simp [refs, srcFound, dstFound, dataToBviRef] at run
                            | some dstEntry =>
                              cases dstEntry with
                              | valueArray values => simp [refs, srcFound, dstFound, dataToBviRef] at run
                              | thunk mode body => simp [refs, srcFound, dstFound, dataToBviRef] at run
                              | mutBlock tag done left child right => simp [refs, srcFound, dstFound, dataToBviRef] at run
                              | byteArray dstFlag dstBytes =>
                                cases copyRun : copyArray (srcBytes, offset) length (some (dstBytes, dstOffset)) with
                                | none => simp [refs, srcFound, dstFound, dataToBviRef, copyRun] at run
                                | some updated =>
                                  simp [refs, srcFound, dstFound, dataToBviRef, BviSem.fromBvl, copyRun] at run
                                  rcases run with ⟨rfl, rfl⟩
                                  refine ⟨{ target with refs := sptInsert dst (.byteArray dstFlag updated) target.refs },
                                    DataSem.unitValue, ?_, dataToBviValue_unit.symm, ?_⟩
                                  · simp [DataSem.doAppAux, DataSem.applyNonFfi, srcFound, dstFound, copyRun]
                                  · simpa [dataToBviRef] using stateRel_insertRef source target related dst (.byteArray dstFlag updated)

end
end Flapjack.Compiler.Backend.BviToData
