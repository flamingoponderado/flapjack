import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppConfigGC
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.MemoryOps

/-! Assignment and reference allocation cases of the primitive simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

namespace DoAppOpassignPort
/-- Roundtrip for the global environment's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end DoAppOpassignPort

/-- The Opassign case of `do_app`; the full theorem is not yet assembled. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Opassign {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .opassign vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.opassign ≠ .aallocEmpty ∧ Op.opassign ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .opassign) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, _, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons value rest =>
      cases rest with
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        cases first <;> simp [doApp, doAppNumericCore, doAppBasic] at run
        case loc flag address =>
          cases assigned : storeAssign address (.refv value) s1.1 with
          | none => simp [assigned] at run
          | some sourceRefs =>
            simp [assigned] at run
            obtain ⟨rfl, rfl⟩ := run
            cases values with
            | cons locationRel tail =>
              cases tail with
              | cons valueRel tail =>
                cases tail
                cases locationRel
                rename_i flatValue
                let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
                have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
                obtain ⟨flatRefs, _, flatApply, relatedUnit, afterRel, reserved⟩ :=
                  opassign_related genv source flat states flag address value flatValue valueRel sourceRefs assigned
                obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
                  (stateRel_iff genv { source with refs := sourceRefs } { flat with refs := flatRefs }).mp afterRel
                refine ⟨.val FlatSem.unitValue, { flat with refs := flatRefs }, afterStores,
                  afterNonempty, afterFfi, rfl, reserved.symm, .value relatedUnit, ?_⟩
                simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatApply]

/-- The Opref case of `do_app`; the full theorem is not yet assembled. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Opref {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .opref vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.opref ≠ .aallocEmpty ∧ Op.opref ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .opref) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, _, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons value rest =>
    cases rest with
    | cons second rest => simp [doApp, doAppNumericCore, doAppBasic] at run
    | nil =>
      cases values with
      | cons valueRel tail =>
        cases tail
        rename_i flatValue
        let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
        have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
        have sim := opref_related genv source flat states value flatValue valueRel
        cases sourceAlloc : storeAlloc (.refv value) s1.1 with
        | mk sourceRefs sourceAddress =>
          simp [doApp, doAppNumericCore, doAppBasic, sourceAlloc] at run
          obtain ⟨rfl, rfl⟩ := run
          cases flatAlloc : storeAlloc (.refv flatValue) flat.refs with
          | mk flatRefs flatAddress =>
            simp only [source, sourceAlloc, flatAlloc] at sim
            obtain ⟨_, flatApply, related, afterRel, reserved⟩ := sim
            obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
              (stateRel_iff genv { source with refs := sourceRefs } { flat with refs := flatRefs }).mp afterRel
            refine ⟨.val (.loc true flatAddress), { flat with refs := flatRefs }, afterStores,
              afterNonempty, afterFfi, rfl, reserved.symm, .value related, ?_⟩
            simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatApply]

end Flapjack.Compiler.Backend.SourceToFlat
