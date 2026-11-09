module

public import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluatePrimitive

@[expose] public section

/-! FFI primitive simulation for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- FFI calls use the same configuration, byte array and FFI state, and
preserve related stores after the call. -/
theorem primitiveSimulation_ffi {C F : Type} (name : Basis.Pure.MlString.MlString) :
    @PrimitiveSimulation C F (.ffi name) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, excRel]
    | cons second tail =>
      cases tail with
      | nil =>
        cases first with
        | byteVector configuration =>
          cases second with
          | refPtr flag index =>
            have refsRel := stateRel_lookupRefs states index
            cases l : source.refs.lookup index with
            | none =>
              cases r : target.refs.lookup index <;> simp_all [optionRel, doApp, excRel]
            | some leftRef =>
              cases r : target.refs.lookup index with
              | none => simp_all [optionRel]
              | some rightRef =>
                have refs : RefRel source.maxApp leftRef rightRef := by
                  simpa [optionRel, l, r] using refsRel
                cases refs with
                | valueArray left right relation => simp [doApp, l, r, excRel]
                | thunk mode left right relation => simp [doApp, l, r, excRel]
                | byteArray bytes =>
                  have ffiEq : target.ffi = source.ffi := states.2.2.2.2.2.2.1
                  simp only [doApp, l, r]
                  rw [ffiEq]
                  cases ffiRun : callFFIHOL source.ffi (.extCall name) configuration bytes with
                  | final event => simp [excRel]
                  | ret ffi updated =>
                    have refs := stateRel_updateRefs states index (.byteArray updated) (.byteArray updated)
                      (.byteArray updated)
                    have next := stateRel_withFfi refs ffi
                    have unitRel : ValueRel source.maxApp unitValue unitValue := .block _ [] [] .nil
                    simp [unitRel, next]
          | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure | partialRecclosure =>
            simp [doApp, excRel]
        | number _ | word64 _ | block _ _ _ _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
          cases second <;> simp [doApp, excRel]
      | cons head tail => simp [doApp, excRel]

end Flapjack.Compiler.Backend.ClosMti
