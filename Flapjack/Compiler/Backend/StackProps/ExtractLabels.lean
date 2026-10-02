import Flapjack.Compiler.Backend.StackLang.Prog

namespace Flapjack.Compiler.Backend.StackProps
open StackLang

/-- Literal ordered label extraction over the complete native StackLang carrier.
Returning calls emit continuation labels before the recursively extracted bodies.
Nonreturning calls ignore the handler field. Repeated labels are retained. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml"
  "extract_labels_def" (words_as_type_indexed_bitvec)]
def extractLabels {width : Nat} [NeZero width] : HolProg width → List (Nat × Nat)
  | .call none _ _ => []
  | .call (some (body, _, l1, l2)) _ handler =>
      match handler with
      | none => [(l1, l2)] ++ extractLabels body
      | some (handlerBody, h1, h2) =>
          [(l1, l2), (h1, h2)] ++ extractLabels body ++ extractLabels handlerBody
  | .loop body => extractLabels body
  | .seq first second => extractLabels first ++ extractLabels second
  | .ite _ _ _ first second => extractLabels first ++ extractLabels second
  | _ => []

end Flapjack.Compiler.Backend.StackProps
