import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux
import Flapjack.Compiler.Backend.Semantics.DataSem.Apply
import Flapjack.Misc.Sptree.Map

/-! FFI primitive simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- A returning FFI call observes the same configuration and byte buffer,
produces the same FFI state, and writes corresponding result bytes. This
factored case is untagged pending review of the complete primitive theorem. -/
theorem doApp_ffi {C F : Type} (name : Basis.Pure.MlString.MlString) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.ffi name) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.ffi name) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
    | cons b rest =>
      cases rest with
      | cons c rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
      | nil =>
        cases a with
        | number n => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | block ts tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | refPtr flag configPtr =>
          cases b with
          | number n => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
          | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
          | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
          | block ts tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
          | refPtr bit ptr =>
            have refs : ∀ key, source.refs.lookup key = (sptLookup key target.refs).map dataToBviRef := by
              intro key
              rw [← sptLookup_sptMap]
              exact related.2.2.2.2.1 key
            cases configFound : sptLookup configPtr target.refs with
            | none => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound] at run
            | some configEntry =>
              cases configEntry with
              | valueArray values => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound] at run
              | thunk mode value => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound] at run
              | mutBlock tag done left child right => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound] at run
              | byteArray immutable config =>
                cases immutable with
                | false => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound] at run
                | true =>
                  cases bytesFound : sptLookup ptr target.refs with
                  | none => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound, bytesFound] at run
                  | some bytesEntry =>
                    cases bytesEntry with
                    | valueArray values => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound, bytesFound] at run
                    | thunk mode value => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound, bytesFound] at run
                    | mutBlock tag done left child right => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound, bytesFound] at run
                    | byteArray mutable bytes =>
                      cases mutable with
                      | true => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound, bytesFound] at run
                      | false =>
                        cases call : callFFIHOL target.ffi (.extCall name) config bytes with
                        | final outcome =>
                          simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound, bytesFound, related.2.2.2.2.2.1, call] at run
                        | ret ffi updated =>
                          simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, BviSem.fromBvl, refs, configFound, bytesFound, related.2.2.2.2.2.1, call] at run
                          rcases run with ⟨rfl, rfl⟩
                          refine ⟨{ target with refs := sptInsert ptr (.byteArray false updated) target.refs, ffi := ffi },
                            DataSem.unitValue, ?_, dataToBviValue_unit.symm, ?_⟩
                          · simp [DataSem.doAppAux, configFound, bytesFound, call]
                          · have inserted := stateRel_insertRef source target related ptr (.byteArray false updated)
                            rcases inserted with ⟨clock, code, oracle, compiler, refsEq, _, global⟩
                            exact ⟨clock, code, oracle, compiler, refsEq, rfl, global⟩

/-- A terminal FFI oracle result is preserved by the complete data dispatcher,
including its space and stack bookkeeping. The lookup and call premises expose
the successful FFI input checks; `doApp_ffi_error` derives the corresponding
result directly from a BVI error. -/
theorem doApp_ffi_final_of_call {C F : Type} (name : Basis.Pure.MlString.MlString)
    (source : BviSem.BviState C F) (target : DataSem.State C F) (related : stateRel source target)
    (flag bit : Bool) (configPtr ptr : Nat) (config bytes : List (BitVec 8)) (event : HolFinalEvent)
    (configFound : sptLookup configPtr target.refs = some (.byteArray true config))
    (bytesFound : sptLookup ptr target.refs = some (.byteArray false bytes))
    (call : callFFIHOL target.ffi (.extCall name) config bytes = .final event) :
    BviSem.doApp (.ffi name) [.refPtr flag configPtr, .refPtr bit ptr] source = .err (.abort (.ffiError event)) ∧
    DataSem.doApp (.ffi name) [.refPtr flag configPtr, .refPtr bit ptr] target = .err (.abort (.ffiError event)) := by
  have refs : ∀ key, source.refs.lookup key = (sptLookup key target.refs).map dataToBviRef := by
    intro key
    rw [← sptLookup_sptMap]
    exact related.2.2.2.2.1 key
  constructor
  · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl,
      refs, configFound, bytesFound, dataToBviRef, related.2.2.2.2.2.1, call]
  · simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSem.doStack, DataSem.doLimSafe,
      DataSem.doAppAux, configFound, bytesFound, call]


/-- A terminal FFI error from BVI is the same terminal error in the full
data dispatcher. This source-shaped local theorem remains untagged pending
review of its state carriers and the underlying FFI dispatchers. -/
theorem doApp_ffi_error {C F : Type} (name : Basis.Pure.MlString.MlString)
    (args : List DataSem.Value) (source : BviSem.BviState C F) (target : DataSem.State C F)
    (event : HolFinalEvent) (related : stateRel source target)
    (run : BviSem.doApp (.ffi name) (args.map dataToBviValue) source = .err (.abort (.ffiError event))) :
    DataSem.doApp (.ffi name) args target = .err (.abort (.ffiError event)) := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
    | cons b rest =>
      cases rest with
      | cons c rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
      | nil =>
        cases a with
        | number n => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | block ts tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | refPtr flag configPtr =>
          cases b with
          | number n => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
          | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
          | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
          | block ts tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
          | refPtr bit ptr =>
            have refs : ∀ key, source.refs.lookup key = (sptLookup key target.refs).map dataToBviRef := by
              intro key
              rw [← sptLookup_sptMap]
              exact related.2.2.2.2.1 key
            cases configFound : sptLookup configPtr target.refs with
            | none => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound] at run
            | some configEntry =>
              cases configEntry with
              | valueArray values => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound] at run
              | thunk mode value => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound] at run
              | mutBlock tag done left child right => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound] at run
              | byteArray immutable config =>
                cases immutable with
                | false => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound] at run
                | true =>
                  cases bytesFound : sptLookup ptr target.refs with
                  | none => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound, bytesFound] at run
                  | some bytesEntry =>
                    cases bytesEntry with
                    | valueArray values => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound, bytesFound] at run
                    | thunk mode value => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound, bytesFound] at run
                    | mutBlock tag done left child right => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound, bytesFound] at run
                    | byteArray mutable bytes =>
                      cases mutable with
                      | true => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound, bytesFound] at run
                      | false =>
                        cases call : callFFIHOL target.ffi (.extCall name) config bytes with
                        | final outcome =>
                          simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, refs, configFound, bytesFound, related.2.2.2.2.2.1, call] at run
                          subst outcome
                          exact (doApp_ffi_final_of_call name source target related flag bit configPtr ptr config bytes event configFound bytesFound call).2
                        | ret ffi updated =>
                          simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, BviSem.fromBvl, refs, configFound, bytesFound, related.2.2.2.2.2.1, call] at run


end
end Flapjack.Compiler.Backend.BviToData
