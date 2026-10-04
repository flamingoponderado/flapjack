import Flapjack.HolRef

namespace Flapjack.Compiler.Backend.BackendCommon

/-- Exact HOL `false_tag_def`. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "false_tag_def"]
def falseTag : Nat := 0

/-- Exact HOL `true_tag_def`. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "true_tag_def"]
def trueTag : Nat := 1

/-- Exact HOL `bool_to_tag_def`. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "bool_to_tag_def"]
def boolToTag (b : Bool) : Nat := if b then trueTag else falseTag

end Flapjack.Compiler.Backend.BackendCommon
