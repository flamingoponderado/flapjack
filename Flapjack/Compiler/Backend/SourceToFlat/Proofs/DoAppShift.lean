import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppConfigGC

/-! The shift case of the source-to-flat primitive simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

namespace DoAppShiftPort
/-- Roundtrip for the global environment's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end DoAppShiftPort

/-- The Shift case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Shift {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (width : WordSize) (shift : Shift) (amount : Nat)
    (vs : List Value) (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 (.shift width shift amount) vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.shift width shift amount ≠ .aallocEmpty ∧ Op.shift width shift amount ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp (.shift width shift amount)) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, _, _, _⟩ := premises
  cases vs with
  | nil => cases width <;> simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | cons second rest => cases width <;> simp [doApp, doAppNumericCore, doAppBasic] at run
    | nil =>
      cases values with
      | cons valueRel tail =>
        cases tail
        cases width <;> cases valueRel <;> simp_all [doApp, doAppNumericCore, doAppBasic]
        all_goals
          rename_i lit _
          cases lit <;> simp_all
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨_, flat, stores, nonempty, rfl, rfl, rfl, ResultRel.value (ValueRel.literal genv _), ?_⟩
          simp [astOpToFlatOp, FlatSem.doApp_shift_projection, FlatSem.applyNumericProjection,
            FlatSem.flatToValue, FlatSem.valueToFlat, doApp, doAppNumericCore, doAppBasic]

end Flapjack.Compiler.Backend.SourceToFlat
