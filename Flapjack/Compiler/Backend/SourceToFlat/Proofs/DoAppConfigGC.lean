module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply
public import Flapjack.SemanticPrimitivesHOL.ApplyNumeric

@[expose] public section

/-! The ConfigGC and Opapp cases of the source-to-flat primitive simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

namespace DoAppConfigGCPort
/-- Roundtrip for the global environment's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end DoAppConfigGCPort

/-- ConfigGC preserves the related stores and FFI, and returns related unit
values. This is the ConfigGC case of `do_app`. The dispatcher inherits the rational-cut real-number assumption
(SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_ConfigGC {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .configGC vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.configGC ≠ .aallocEmpty ∧ Op.configGC ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .configGC) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, _, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        cases values with
        | cons firstRel tail =>
          cases tail with
          | cons secondRel tail =>
            cases tail
            cases firstRel <;> cases secondRel <;>
              simp_all [doApp, doAppNumericCore, doAppBasic]
            case literal.literal lit1 lit2 _ =>
              cases lit1 <;> cases lit2 <;> simp_all
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨.val FlatSem.unitValue, flat, stores, nonempty, rfl, rfl, rfl, ?_, ?_⟩
              · exact ResultRel.value (ValueRel.tuple genv [] [] (.nil genv))
              · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric,
                  FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.unitValue]

/-- The Opapp case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Opapp {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .opapp vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.opapp ≠ .aallocEmpty ∧ Op.opapp ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .opapp) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, _⟩ := premises
  simp [doApp, doAppNumericCore, doAppBasic] at run

end Flapjack.Compiler.Backend.SourceToFlat
