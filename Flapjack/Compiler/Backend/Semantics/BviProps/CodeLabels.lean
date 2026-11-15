module

public import Flapjack.Compiler.Backend.Bvi.Syntax
public import Flapjack.Compiler.Backend.ClosLang.CodeLabels
public import Mathlib.Data.Set.Lattice

@[expose] public section

/-! Code labels referenced by BVI expressions. -/
namespace Flapjack.Compiler.Backend.BviProps

mutual
/-- The code labels referenced by a BVI expression. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "get_code_labels_def" 696]
def getCodeLabels : Bvi.Exp → Set Nat
  | .var _ => ∅
  | .ifThenElse a b c => getCodeLabels a ∪ getCodeLabels b ∪ getCodeLabels c
  | .let es body => getCodeLabelsList es ∪ getCodeLabels body
  | .raise body => getCodeLabels body
  | .tick body => getCodeLabels body
  | .force loc _ => {loc}
  | .call _ dest es handler =>
      (match dest with | none => ∅ | some loc => {loc}) ∪
        (match handler with | none => ∅ | some body => getCodeLabels body) ∪ getCodeLabelsList es
  | .op op es => ClosLang.assignGetCodeLabel op ∪ getCodeLabelsList es
  | .return es => getCodeLabelsList es
  | .letCall _ _ dest es body => {dest} ∪ getCodeLabels body ∪ getCodeLabelsList es

/-- Structural list helper for HOL's mapped union, used in the recursive
definition; it has no separate HOL declaration. -/
def getCodeLabelsList : List Bvi.Exp → Set Nat
  | [] => ∅
  | e :: es => getCodeLabels e ∪ getCodeLabelsList es
end

/-- The structural list helper is the original mapped union. This is
Flapjack-specific support for the recursive definition. -/
theorem getCodeLabelsList_eq (es : List Bvi.Exp) :
    getCodeLabelsList es = ⋃₀ (getCodeLabels '' {e | e ∈ es}) := by
  induction es with
  | nil => simp [getCodeLabelsList]
  | cons e es ih =>
    ext label
    simp [getCodeLabelsList, ih]

/-- Every referenced code label is defined by the program or allowed
externally. The middle program-entry payload remains polymorphic. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "good_code_labels_def"]
def goodCodeLabels {α : Type} (program : List (Nat × α × Bvi.Exp))
    (external : Set Nat) : Prop :=
  (⋃₀ ((fun entry => getCodeLabels entry.2.2) '' {entry | entry ∈ program})) ⊆
    {label | label ∈ program.map Prod.fst} ∪ external

end Flapjack.Compiler.Backend.BviProps
