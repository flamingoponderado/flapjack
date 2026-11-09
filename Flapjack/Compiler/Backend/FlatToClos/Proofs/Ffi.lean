module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.CopyUpdate

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
import all Flapjack.Compiler.Backend.Semantics.FlatSem.Evaluate
import all Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact
@[expose] public section

/-! FFI cases for the proof-side flat-to-closure simulation. These lemmas
are Flapjack infrastructure and have not been reviewed as HOL ports. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- A returning FFI call updates corresponding byte arrays and external
states on both sides. This is part of HOL's `op_ffi` proof and has no
separately named HOL declaration. -/
theorem ffiReturn_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (pointer : Nat) (flag : Bool)
    (bytes updated : List HolChar) (configuration name : MlString)
    (ffi : Flapjack.HolFfiState F) (states : StateRel source target)
    (found : storeLookup pointer source.refs = some (.w8array bytes))
    (call : Flapjack.callFFIHOL source.ffi (.extCall name) configuration.explode bytes = .ret ffi updated) :
    ∃ targetNext,
      FlatSem.doAppData source (.ffi name) [.litv (.strLit configuration), .loc flag pointer] =
        some (some ({ source with refs := source.refs.set pointer (.w8array updated), ffi := ffi }, .val FlatSem.unitValue)) ∧
      ClosSem.doApp (.ffi name) [.byteVector configuration.explode, .refPtr flag pointer] target =
        .val (ClosSem.unitValue, targetNext) ∧
      StateRel { source with refs := source.refs.set pointer (.w8array updated), ffi := ffi } targetNext := by
  have targetFound := lookup_byteArray states found
  have foundList : source.refs[pointer]? = some (.w8array bytes) := by simpa [storeLookup] using found
  have newStores := storeRel_setByteArray source.refs target.refs pointer bytes updated states.2.2.2.1 foundList
  have targetCall : Flapjack.callFFIHOL target.ffi (.extCall name) configuration.explode bytes = .ret ffi updated := by
    rw [← states.2.1]
    exact call
  refine ⟨{ target with refs := target.refs.updateEq (pointer, .byteArray updated), ffi := ffi }, ?_, ?_, ?_⟩
  · simp [FlatSem.doAppData, storeLookup, foundList, call, storeAssign, storeValueSameType]
  · simp [ClosSem.doApp, targetFound, targetCall]
  · rcases states with ⟨maxApp, _, clock, _, globals, values, install⟩
    exact ⟨maxApp, rfl, clock, newStores, globals, values, install⟩

end Flapjack.Compiler.Backend.FlatToClos
