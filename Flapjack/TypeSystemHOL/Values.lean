import Flapjack.AstHOL.Syntax

/-! The source value predicate used by declarative typing and inference. -/
namespace Flapjack.TypeSystemHOL

mutual
@[hol "cakeml/semantics/typeSystemScript.sml" "is_value_def"]
def isValue : AstHOL.Exp → Bool
  | .lit _ | .var _ | .fn _ _ => true
  | .con _ es => isValueList es
  | .tannot e _ | .lannot e _ => isValue e
  | _ => false
termination_by e => sizeOf e

/-- Flapjack mutual-recursion helper for the value predicate on lists. -/
def isValueList : List AstHOL.Exp → Bool
  | [] => true
  | e :: es => isValue e && isValueList es
termination_by es => sizeOf es
end

end Flapjack.TypeSystemHOL
