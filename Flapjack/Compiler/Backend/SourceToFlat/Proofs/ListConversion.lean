import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRel
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalEnvConditions
import Flapjack.Compiler.Backend.Semantics.FlatSem.Conversions
import Flapjack.SemanticPrimitivesHOL.Conversions

/-! List conversion compatibility over the factored source-to-flat relation.
The relation's full correspondence to HOL remains open. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon
open Flapjack.Basis.Pure.MlString

/-- Related lists encode to related source and flat list values when the
constructor map contains the list stamps. This is Flapjack infrastructure
over the factored relation, not a tagged HOL theorem. -/
theorem listToValue_related (genv : GlobalEnv) (hasLists : hasLists genv.c)
    (xs : List SemanticPrimitivesHOL.Value) (ys : List FlatSem.Value)
    (related : List.Forall₂ (ValueRel genv) xs ys) :
    ValueRel genv (SemanticPrimitivesHOL.listToValue xs) (FlatSem.listToValue ys) := by
  induction related with
  | nil =>
    apply ValueRel.constructor
    · exact .nil genv
    · exact hasLists.2
  | cons head tail ih =>
    apply ValueRel.constructor
    · exact .cons genv _ _ _ _ head (.cons genv _ _ _ _ ih (.nil genv))
    · exact hasLists.1

/-- Concatenating related lists of values gives the same optional string.
This is Flapjack infrastructure over the factored relation. -/
theorem valuesToString_related (genv : GlobalEnv)
    (xs : List SemanticPrimitivesHOL.Value) (ys : List FlatSem.Value)
    (related : List.Forall₂ (ValueRel genv) xs ys) :
    SemanticPrimitivesHOL.valuesToString xs = FlatSem.valuesToString ys := by
  induction related with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> try (rfl)
    case literal lit => cases lit <;> simp [SemanticPrimitivesHOL.valuesToString, FlatSem.valuesToString, ih]

end Flapjack.Compiler.Backend.SourceToFlat
