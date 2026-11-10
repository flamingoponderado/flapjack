module

public import Flapjack.Compiler.Backend.Bvl.Syntax
public import Flapjack.Compiler.Backend.ClosLang.CodeLabels
public import Mathlib.Data.Set.Lattice

@[expose] public section

/-! Code labels referenced by BVL expressions. -/
namespace Flapjack.Compiler.Backend.BvlProps

mutual
/-- The code labels referenced by a BVL expression. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "get_code_labels_def" 878]
def getCodeLabels : Bvl.Exp → Set Nat
  | .var _ => ∅
  | .ifThenElse a b c => getCodeLabels a ∪ getCodeLabels b ∪ getCodeLabels c
  | .let es body => getCodeLabelsList es ∪ getCodeLabels body
  | .raise body => getCodeLabels body
  | .handle body handler => getCodeLabels body ∪ getCodeLabels handler
  | .tick body => getCodeLabels body
  | .force loc _ => {loc}
  | .call _ dest es => (match dest with | none => ∅ | some loc => {loc}) ∪ getCodeLabelsList es
  | .op op es => ClosLang.assignGetCodeLabel op ∪ getCodeLabelsList es

/-- Flapjack's structural list helper for HOL's `BIGUNION (set (MAP ...))`. -/
def getCodeLabelsList : List Bvl.Exp → Set Nat
  | [] => ∅
  | e :: es => getCodeLabels e ∪ getCodeLabelsList es
end

/-- The structural list helper is HOL's mapped union; this comparison lemma
is Flapjack-specific infrastructure for the recursive definition. -/
theorem getCodeLabelsList_eq (es : List Bvl.Exp) :
    getCodeLabelsList es = ⋃₀ (getCodeLabels '' {e | e ∈ es}) := by
  induction es with
  | nil => simp [getCodeLabelsList]
  | cons e es ih =>
    ext label
    simp [getCodeLabelsList, ih]

end Flapjack.Compiler.Backend.BvlProps
