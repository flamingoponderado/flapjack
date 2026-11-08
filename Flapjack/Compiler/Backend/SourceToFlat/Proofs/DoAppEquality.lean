import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppConfigGC
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.Equality

/-! The equality case of the source-to-flat primitive simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

namespace DoAppEqualityPort
/-- Roundtrip for the global environment's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end DoAppEqualityPort

/-- The Equality case of `do_app`; the full theorem is not yet assembled. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Equality {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .equality vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.equality ≠ .aallocEmpty ∧ Op.equality ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .equality) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
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
            rename_i flatFirst flatSecond
            have eqPreserved := equality_preserved genv ok first second flatFirst flatSecond firstRel secondRel
            cases eq : SemanticPrimitivesHOL.doEq first second with
            | typeError => simp [doApp, doAppNumericCore, doAppBasic, eq] at run
            | val b =>
              simp only [doApp, doAppNumericCore, doAppBasic, eq] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨.val (FlatSem.boolValue b), flat, stores, nonempty, ffi, rfl, rfl, ?_, ?_⟩
              · exact .value ((boolValueRel_iff genv b _ ok).mpr rfl)
              · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, eqPreserved, eq]

end Flapjack.Compiler.Backend.SourceToFlat
