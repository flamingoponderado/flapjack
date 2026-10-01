import Flapjack.HolRef
import Flapjack.Pancake.WordLang
import Mathlib.Data.Set.Basic

namespace Flapjack

/-- Literal source-program code references from HOL wordConvs. Both populated
Call bodies are traversed independently, including a handler on a nonreturning
Call. Continuation metadata is excluded; LocValue contributes its code label. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml"
  "get_code_labels_def" (words_as_type_indexed_bitvec)]
def getCodeLabelsHOL {width : Nat} [NeZero width] :
    WordLangProgHOL (BitVec width) → Set Nat
  | .call returns target _ handler =>
      (match target with
        | some label => {label}
        | none => ∅) ∪
      (match returns with
        | some (_, _, body, _, _) => getCodeLabelsHOL body
        | none => ∅) ∪
      (match handler with
        | some (_, body, _, _) => getCodeLabelsHOL body
        | none => ∅)
  | .seq first second => getCodeLabelsHOL first ∪ getCodeLabelsHOL second
  | .loop _ body _ => getCodeLabelsHOL body
  | .ite _ _ _ first second => getCodeLabelsHOL first ∪ getCodeLabelsHOL second
  | .mustTerminate body => getCodeLabelsHOL body
  | .locValue _ label => {label}
  | _ => ∅

end Flapjack
