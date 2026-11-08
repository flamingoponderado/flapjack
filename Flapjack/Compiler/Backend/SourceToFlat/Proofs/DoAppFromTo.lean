import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppConfigGC
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveArith

/-! The conversion case of the source-to-flat primitive simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

namespace DoAppFromToPort
/-- Roundtrip for the global environment's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end DoAppFromToPort

/-- The FromTo case of `do_app`; the full theorem is not yet assembled. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_FromTo {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (fromType toType : PrimType)
    (vs : List Value) (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 (.fromTo fromType toType) vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.fromTo fromType toType ≠ .aallocEmpty ∧ Op.fromTo fromType toType ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp (.fromTo fromType toType)) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  cases vs with
  | nil =>
    cases fromType <;> cases toType <;> (try cases ‹WordSize›) <;> (try cases ‹WordSize›) <;>
      simp [doApp, doAppNumericCore] at run
  | cons operand rest =>
    cases rest with
    | cons second rest =>
      cases fromType <;> cases toType <;> (try cases ‹WordSize›) <;> (try cases ‹WordSize›) <;>
        simp [doApp, doAppNumericCore] at run
    | nil =>
      let source : SemanticPrimitivesHOL.State F := ⟨0, s1.1, s1.2, 0, 0, none⟩
      have successful : doApp (source.refs, source.ffi) (.fromTo fromType toType) [operand] ≠ none := by
        simp [source, run]
      obtain ⟨lit, rfl⟩ := conversion_operand source fromType toType operand successful
      cases values with
      | cons operandRel tail =>
        cases tail
        cases operandRel
        have sim := conversion_related genv ok source flat fromType toType lit
        simp only [source, run] at sim
        cases targetEq : FlatSem.doAppNumeric flat (.fromTo fromType toType) [.litv lit] with
        | none => simp [targetEq] at sim
        | some out =>
          cases out with
          | none => simp [targetEq] at sim
          | some pair =>
            obtain ⟨next, result⟩ := pair
            simp only [targetEq] at sim
            obtain ⟨refs, nextFfi, nextState, rel⟩ := sim
            subst next
            refine ⟨result, flat, ?_, nonempty, ?_, rfl, rfl, rel, ?_⟩
            · simpa [refs] using stores
            · exact nextFfi.trans ffi
            · simp [astOpToFlatOp, FlatSem.doApp, targetEq]

end Flapjack.Compiler.Backend.SourceToFlat
