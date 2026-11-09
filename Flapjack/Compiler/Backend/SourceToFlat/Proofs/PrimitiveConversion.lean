module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveType
public import Flapjack.SemanticPrimitivesProps.Conversion

@[expose] public section

/-! Conversion cases for the source-to-flat primitive simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

namespace ConversionPort
/-- Roundtrip for the global environment's finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end ConversionPort

/-- A conversion exception is the character-range exception and is preserved
by the source-to-flat value projection. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_conversion_INL"
  (fmap_as_finite_support := [c, tys])]
theorem doConversion_inl (sourceType : PrimType) (v : SemanticPrimitivesHOL.Value)
    (genv : GlobalEnv) (flat : FlatSem.Value) (targetType : PrimType) (exn : SemanticPrimitivesHOL.Value)
    (premises : checkType sourceType v = true ∧ genvCOk genv.c ∧ ValueRel genv v flat ∧
      doConversion v sourceType targetType = some (.inl exn)) :
    exn = chrExnV ∧ checkType sourceType (FlatSem.flatToValue flat) = true ∧
      ∃ e, doConversion (FlatSem.flatToValue flat) sourceType targetType = some (.inl e) := by
  obtain ⟨checked, ok, related, converted⟩ := premises
  have equal := checked_flatToValue_related genv sourceType v flat ⟨checked, related, ok⟩
  have exception : exn = chrExnV := by
    cases sourceType <;> try (rename_i width; cases width)
    all_goals cases targetType <;> try (rename_i width; cases width)
    all_goals simp [doConversion] at converted
    all_goals split at converted <;> simp_all
  rw [equal]
  exact ⟨exception, checked, exn, converted⟩

/-- A successful conversion retains the source-to-flat value relation. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_conversion_INR"
  (fmap_as_finite_support := [c, tys])]
theorem doConversion_inr (sourceType : PrimType) (v : SemanticPrimitivesHOL.Value)
    (genv : GlobalEnv) (flat : FlatSem.Value) (targetType : PrimType) (result : SemanticPrimitivesHOL.Value)
    (premises : checkType sourceType v = true ∧ genvCOk genv.c ∧ ValueRel genv v flat ∧
      doConversion v sourceType targetType = some (.inr result)) :
    checkType sourceType (FlatSem.flatToValue flat) = true ∧
      ∃ result', doConversion (FlatSem.flatToValue flat) sourceType targetType = some (.inr result') ∧
        ValueRel genv result (FlatSem.valueToFlat result') := by
  obtain ⟨checked, ok, related, converted⟩ := premises
  have equal := checked_flatToValue_related genv sourceType v flat ⟨checked, related, ok⟩
  rw [equal]
  exact ⟨checked, result, converted,
    checked_valueToFlat_related genv targetType result
      ⟨Flapjack.SemanticPrimitivesProps.doConversion_checkType v sourceType targetType result converted, ok⟩⟩

end Flapjack.Compiler.Backend.SourceToFlat
