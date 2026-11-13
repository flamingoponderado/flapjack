module

public import Flapjack.Compiler.Backend.ClosLang.CodeLabels
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Order

@[expose] public section

/-! Code labels referenced by closure-language expressions. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosLang

mutual
/-- The code labels referenced by a closure expression. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "get_code_labels_def" 3694]
def getCodeLabels : Exp → Set Nat
  | .var .. => ∅
  | .ifThenElse _ x y z => getCodeLabels x ∪ getCodeLabels y ∪ getCodeLabels z
  | .let _ es body => getCodeLabelsList es ∪ getCodeLabels body
  | .raise _ body => getCodeLabels body
  | .handle _ body handler => getCodeLabels body ∪ getCodeLabels handler
  | .tick _ body => getCodeLabels body
  | .call _ _ loc es => {loc} ∪ getCodeLabelsList es
  | .app _ loc body es =>
      (match loc with | none => ∅ | some n => {n}) ∪ getCodeLabels body ∪ getCodeLabelsList es
  | .fn _ loc _ _ body => (match loc with | none => ∅ | some n => {n}) ∪ getCodeLabels body
  | .letrec _ loc _ funs body =>
      (match loc with | none => ∅ | some n => (fun k => n + 2 * k) '' Set.Iio funs.length) ∪
        getCodeLabels body ∪ getCodeLabelsFuns funs
  | .op _ op es => getCodeLabelsList es ∪ assignGetCodeLabel op
termination_by e => sizeOf e

/-- Structural rendering of HOL's union over a mapped expression list. -/
def getCodeLabelsList : List Exp → Set Nat
  | [] => ∅
  | e :: es => getCodeLabels e ∪ getCodeLabelsList es
termination_by es => sizeOf es

/-- Structural rendering of the union over recursive-function bodies. -/
def getCodeLabelsFuns : List (Nat × Exp) → Set Nat
  | [] => ∅
  | (_, body) :: funs => getCodeLabels body ∪ getCodeLabelsFuns funs
termination_by funs => sizeOf funs
end

/-- The list helper equals HOL's mapped union; this Flapjack-specific
equation justifies the recursive implementation. -/
theorem getCodeLabelsList_eq (es : List Exp) :
    getCodeLabelsList es = ⋃₀ (getCodeLabels '' {e | e ∈ es}) := by
  induction es with
  | nil => simp [getCodeLabelsList]
  | cons e es ih => ext label; simp [getCodeLabelsList, ih]

/-- The recursive-function helper is the original traversal over `MAP SND`.
This Flapjack-specific equation supports the source comparison. -/
theorem getCodeLabelsFuns_eq (funs : List (Nat × Exp)) :
    getCodeLabelsFuns funs = getCodeLabelsList (funs.map Prod.snd) := by
  induction funs with
  | nil => simp [getCodeLabelsFuns, getCodeLabelsList]
  | cons entry funs ih => cases entry; simp [getCodeLabelsFuns, getCodeLabelsList, ih]

end Flapjack.Compiler.Backend.ClosProps
