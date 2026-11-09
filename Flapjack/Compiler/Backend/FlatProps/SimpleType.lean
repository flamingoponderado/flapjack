module

public import Flapjack.Compiler.Backend.FlatProps.SimpleRelations
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Primitives

@[expose] public section
/-! Primitive type checks for simple flat value relations.
The private single-value lemma supports the local HOL list theorem. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL
private theorem checkedValueEq (vr : Value → Value → Prop) (ty : PrimType) (x y : Value)
    (simple : simpleValueRel vr) (related : vr x y)
    (checked : Flapjack.SemanticPrimitivesHOL.checkType ty (flatToValue x) = true) : y = x := by
  cases x with
  | litv literal =>
    have nonclosure : ¬ isClosure (.litv literal) := by simp [isClosure]
    have basic := ((simple.2 _ _ nonclosure).mp related).1
    exact basic
  | conv stamp values =>
    have nonclosure : ¬ isClosure (.conv stamp values) := by simp [isClosure]
    have shape := (simple.2 _ _ nonclosure).mp related
    obtain ⟨other, eq⟩ := shape.1
    subst y
    cases values with
    | nil =>
      cases other with
      | nil => rfl
      | cons => cases shape.2
    | cons value rest =>
      cases ty <;> simp [flatToValue, Flapjack.SemanticPrimitivesHOL.checkType] at checked
  | closure env name body =>
    cases ty <;> simp [flatToValue, Flapjack.SemanticPrimitivesHOL.checkType] at checked
  | recclosure env functions name =>
    cases ty <;> simp [flatToValue, Flapjack.SemanticPrimitivesHOL.checkType] at checked
  | loc flag index =>
    cases ty <;> simp [flatToValue, Flapjack.SemanticPrimitivesHOL.checkType] at checked
  | vectorv values =>
    cases ty <;> simp [flatToValue, Flapjack.SemanticPrimitivesHOL.checkType] at checked

/-- Related, primitive-typed value lists agree element by element. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "check_type_LIST_REL_same"]
theorem checkType_listRel_same (vr : Value → Value → Prop) (vs1 vs2 : List Value) (ty : PrimType)
    (premises : List.Forall₂ vr vs1 vs2 ∧
      (vs1.map flatToValue).all (Flapjack.SemanticPrimitivesHOL.checkType ty) = true ∧
      simpleValueRel vr) : vs2 = vs1 := by
  obtain ⟨related, checked, simple⟩ := premises
  induction related with
  | nil => rfl
  | cons hrel hrest ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at checked
    have headEq := checkedValueEq vr ty _ _ simple hrel checked.1
    have tailEq := ih checked.2
    simp only [headEq, tailEq]
end Flapjack.Compiler.Backend.FlatProps
