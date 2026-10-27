import Flapjack.SemanticPrimitivesHOL

/-! First-order source values used by dynamic compilation. Statement review is pending. -/
namespace Flapjack.SemanticPrimitivesHOL

mutual
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "concrete_v_def"]
def concreteValue (value : Value) : Bool :=
  match value with
  | .loc _ _ | .litv _ => true
  | .conv _ values | .vectorv values => concreteValues values
  | _ => false
termination_by sizeOf value

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "concrete_v_def"]
def concreteValues (values : List Value) : Bool :=
  match values with
  | [] => true
  | value :: rest => concreteValue value && concreteValues rest
termination_by sizeOf values
end

end Flapjack.SemanticPrimitivesHOL
