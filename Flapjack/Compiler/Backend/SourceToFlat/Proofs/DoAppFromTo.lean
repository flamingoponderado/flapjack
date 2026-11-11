module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppConfigGC
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveConversion
public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyArithmeticSource

@[expose] public section

/-! The conversion case of the source-to-flat primitive simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

namespace DoAppFromToPort
/-- Roundtrip for the global environment's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end DoAppFromToPort

/-- The FromTo case of `do_app`; the full theorem is `doApp_correct`. The
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
  | nil => simp [doApp] at run
  | cons operand rest =>
    cases rest with
    | cons second rest => simp [doApp] at run
    | nil =>
      cases values with
      | cons related tail =>
        cases tail
        rename_i flatOperand
        simp only [SemanticPrimitivesHOL.doApp] at run
        split at run
        next checked =>
          cases converted : doConversion operand fromType toType with
          | none => simp [converted] at run
          | some result =>
            cases result with
            | inl error =>
              simp only [converted, Option.map_some, Option.some.injEq, Prod.mk.injEq] at run
              obtain ⟨rfl, rfl⟩ := run
              obtain ⟨errorEq, flatChecked, flatError, flatConverted⟩ :=
                doConversion_inl fromType operand genv flatOperand toType error ⟨checked, ok, related, converted⟩
              subst error
              refine ⟨.err (.raise FlatSem.chrExnV), flat, stores, nonempty, ffi, rfl, rfl, ?_, ?_⟩
              · exact .raise (valueRel_lemmas genv ok).2.2.1
              · simp [astOpToFlatOp, FlatSem.doApp_conversion_source, flatChecked, flatConverted]
            | inr value =>
              simp only [converted, Option.map_some, Option.some.injEq, Prod.mk.injEq] at run
              obtain ⟨rfl, rfl⟩ := run
              obtain ⟨flatChecked, flatValue, flatConverted, resultRel⟩ :=
                doConversion_inr fromType operand genv flatOperand toType value ⟨checked, ok, related, converted⟩
              refine ⟨.val (FlatSem.valueToFlat flatValue), flat, stores, nonempty, ffi, rfl, rfl, .value resultRel, ?_⟩
              simp [astOpToFlatOp, FlatSem.doApp_conversion_source, flatChecked, flatConverted]
        next => simp at run

end Flapjack.Compiler.Backend.SourceToFlat
