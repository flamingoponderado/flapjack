module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveType
public import Flapjack.SemanticPrimitivesProps.Arithmetic

@[expose] public section

/-! Arithmetic result cases for the source-to-flat primitive simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

namespace ArithmeticPort
/-- Roundtrip for the global environment's finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end ArithmeticPort

/-- Arithmetic exceptions are division exceptions and survive projection to
source values. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_arith_INL"
  (fmap_as_finite_support := [c, tys])]
theorem doArith_inl (typ : PrimType) (values : List SemanticPrimitivesHOL.Value)
    (genv : GlobalEnv) (flatValues : List FlatSem.Value) (action : Arith) (exn : SemanticPrimitivesHOL.Value)
    (premises : values.all (checkType typ) = true ∧ genvCOk genv.c ∧
      List.Forall₂ (ValueRel genv) values flatValues ∧ doArith action typ values = some (.inl exn)) :
    exn = divExnV ∧ (flatValues.map FlatSem.flatToValue).all (checkType typ) = true ∧
      ∃ e, doArith action typ (flatValues.map FlatSem.flatToValue) = some (.inl e) := by
  obtain ⟨checked, ok, related, evaluated⟩ := premises
  have equal := checked_flatToValue_list genv typ values flatValues ⟨checked, related, ok⟩
  have exception := Flapjack.SemanticPrimitivesProps.doArith_exception action typ values exn evaluated
  rw [equal]
  exact ⟨exception, checked, exn, evaluated⟩

/-- Successful arithmetic retains the source-to-flat value relation. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_arith_INR"
  (fmap_as_finite_support := [c, tys])]
theorem doArith_inr (typ : PrimType) (values : List SemanticPrimitivesHOL.Value)
    (genv : GlobalEnv) (flatValues : List FlatSem.Value) (action : Arith) (result : SemanticPrimitivesHOL.Value)
    (premises : values.all (checkType typ) = true ∧ genvCOk genv.c ∧
      List.Forall₂ (ValueRel genv) values flatValues ∧ doArith action typ values = some (.inr result)) :
    (flatValues.map FlatSem.flatToValue).all (checkType typ) = true ∧
      ∃ result', doArith action typ (flatValues.map FlatSem.flatToValue) = some (.inr result') ∧
        ValueRel genv result (FlatSem.valueToFlat result') := by
  obtain ⟨checked, ok, related, evaluated⟩ := premises
  have equal := checked_flatToValue_list genv typ values flatValues ⟨checked, related, ok⟩
  rw [equal]
  exact ⟨checked, result, evaluated,
    checked_valueToFlat_related genv typ result
      ⟨Flapjack.SemanticPrimitivesProps.doArith_checkType action typ values result evaluated, ok⟩⟩

end Flapjack.Compiler.Backend.SourceToFlat
