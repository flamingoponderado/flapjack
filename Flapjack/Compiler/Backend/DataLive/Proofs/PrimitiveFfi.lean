module

public import Flapjack.Compiler.Backend.DataLive.Proofs.PrimitiveGlobal

@[expose] public section

/-! FFI primitive simulation for the liveness pass. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Updating the reference store and FFI state identically preserves the
liveness relation. This is auxiliary proof infrastructure. -/
theorem stateRel_setRefsFfi {C F : Type} (source target : State C F) (live : NumSet)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (ffi : HolFfiState F) (related : stateRel source target live) :
    stateRel { source with refs := refs, ffi := ffi } { target with refs := refs, ffi := ffi } live := by
  rcases related with ⟨code, clock, space, _, _, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
  exact ⟨code, clock, space, rfl, rfl, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩

/-- Related states make the same FFI call and receive matching results.
This remains untagged pending source evaluator and carrier review. -/
theorem stateRel_doAppAux_ffi {C F : Type} (source target : State C F) (live : NumSet)
    (name : Basis.Pure.MlString.MlString) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.ffi name) args source) (doAppAux (.ffi name) args target) := by
  have refs := related.2.2.2.2.1
  have ffi := related.2.2.2.1
  cases args with
  | nil => simp [doAppAux, appRel]
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, appRel]
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, appRel]
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, appRel]
        case refPtr.refPtr flag configPtr bit ptr =>
          cases configFound : sptLookup configPtr source.refs with
          | none => simp [configFound, ← refs]
          | some configEntry =>
            cases configEntry <;> simp [configFound, ← refs]
            case byteArray immutable config =>
              cases immutable with
              | false => simp
              | true =>
                cases bytesFound : sptLookup ptr source.refs with
                | none => simp
                | some bytesEntry =>
                  cases bytesEntry <;> try simp
                  case byteArray mutable bytes =>
                    cases mutable with
                    | true => simp
                    | false =>
                      cases call : callFFIHOL source.ffi (.extCall name) config bytes with
                      | final outcome => simp [call, ← ffi]
                      | ret nextFfi updated =>
                        simpa [call, ← ffi, ← refs, appRel] using
                          stateRel_setRefsFfi source target live (sptInsert ptr (.byteArray false updated) source.refs) nextFfi related

/-- Related states produce matching FFI outcomes through the full primitive
dispatcher, including space and stack accounting. -/
theorem stateRel_doApp_ffi {C F : Type} (source target : State C F) (live : NumSet)
    (name : Basis.Pure.MlString.MlString) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doApp (.ffi name) args source) (doApp (.ffi name) args target) := by
  simp only [doApp]
  rcases stateRel_doSpace source target live (.ffi name) args related with failed | ⟨sourceNext, targetNext, sourceRun, targetRun, nextRel⟩
  · simp [failed.1, failed.2, appRel]
  · simp only [sourceRun, targetRun]
    exact stateRel_doAppAux_ffi _ _ live name args (stateRel_doStackLim sourceNext targetNext live (.ffi name) args nextRel)

/-- FFI assignments satisfy the liveness simulation with or without a
live-name annotation. The unannotated form is a type error in the source. -/
theorem simulationFor_assign_ffi_all {C F : Type} (dest : Nat) (name : Basis.Pure.MlString.MlString)
    (args : List Nat) (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.ffi name) args names) live := by
  cases names with
  | none => exact simulationFor_removed_requiresNames dest (.ffi name) args live rfl
  | some names =>
    apply simulationFor_annotated_of_appRel dest (.ffi name) args names live
    intro source target values related
    exact stateRel_doApp_ffi source target _ name values related

end Flapjack.Compiler.Backend.DataLive
