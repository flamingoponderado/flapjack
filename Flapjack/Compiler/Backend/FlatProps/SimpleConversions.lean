import Flapjack.Compiler.Backend.FlatProps.SimpleRelations
import Flapjack.Compiler.Backend.Semantics.FlatSem.Conversions

/-! List conversion properties for simple flat value relations. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem

/-- Encoding pointwise related lists produces related flat values. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_v_rel_list_to_v"]
theorem simpleListToValue (relation : Value → Value → Prop)
    (simple : simpleValueRel relation) (left right : List Value)
    (related : List.Forall₂ relation left right) :
    relation (listToValue left) (listToValue right) := by
  induction related with
  | nil =>
    apply (simple.2 _ _ (by simp [listToValue, isClosure])).2
    simp [listToValue, simpleBasicValRel, valueContainerXs]
  | cons head tail ih =>
    apply (simple.2 _ _ (by simp [listToValue, isClosure])).2
    constructor
    · simp [listToValue, simpleBasicValRel]
    · simpa [listToValue, valueContainerXs] using List.Forall₂.cons head (List.Forall₂.cons ih List.Forall₂.nil)


/-- Concatenating pointwise related string literals preserves the result. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_vs_to_string_v_rel"]
theorem simpleValuesToString (relation : Value → Value → Prop)
    (simple : simpleValueRel relation) (values values' : List Value)
    (result : Flapjack.Basis.Pure.MlString.MlString)
    (related : List.Forall₂ relation values values')
    (run : valuesToString values = some result) :
    valuesToString values' = some result := by
  induction related generalizing result with
  | nil => simpa [valuesToString] using run
  | @cons value value' tail tail' valueRel tailRel ih =>
    cases value with
    | litv literal =>
      have shape := ((simple.2 _ _ (by simp [isClosure])).1 valueRel).1
      have eq : value' = .litv literal := by simpa [simpleBasicValRel] using shape
      subst value'
      cases literal with
      | strLit string =>
        cases tailRun : valuesToString tail with
        | none => simp [valuesToString, tailRun] at run
        | some rest =>
          have targetTail := ih rest tailRun
          simpa [valuesToString, tailRun, targetTail] using run
      | intLit _ | word8 _ | word64 _ | char _ | float64 _ => simp [valuesToString] at run
    | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ => simp [valuesToString] at run

end Flapjack.Compiler.Backend.FlatProps
