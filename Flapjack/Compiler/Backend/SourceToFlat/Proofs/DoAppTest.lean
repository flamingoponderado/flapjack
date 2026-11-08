import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppConfigGC
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveTest

/-! The Test case of the source-to-flat primitive simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

namespace DoAppTestPort
/-- Roundtrip for the global environment's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end DoAppTestPort

/-- The Test case of `do_app`; the full theorem is not yet assembled. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Test {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (test : Test) (typ : PrimType)
    (vs : List Value) (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 (.test test typ) vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.test test typ ≠ .aallocEmpty ∧ Op.test test typ ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp (.test test typ)) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [doApp] at run
      | nil =>
        cases values with
        | cons firstRel tail =>
          cases tail with
          | cons secondRel tail =>
            cases tail
            rename_i flatFirst flatSecond
            cases comparison : SemanticPrimitivesHOL.doTest test typ first second with
            | typeError => simp [doApp, comparison] at run
            | val b =>
              have flatComparison := doTest_related test typ first second b genv flatFirst flatSecond
                ⟨comparison, ok, firstRel, secondRel⟩
              simp only [doApp, comparison] at run
              obtain ⟨rfl, rfl⟩ := Option.some.inj run
              refine ⟨.val (FlatSem.boolValue b), flat, stores, nonempty, ffi, rfl, rfl, ?_, ?_⟩
              · exact .value ((boolValueRel_iff genv b _ ok).mpr rfl)
              · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatComparison]

end Flapjack.Compiler.Backend.SourceToFlat
