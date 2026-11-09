import Flapjack.Compiler.Backend.Semantics.ClosSem
import Mathlib.Data.List.Forall2

/-! Relations on closure-language reference values. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem

/-- Relate value arrays elementwise, byte arrays by equality, and thunks by
mode and their contained values. The contained value types are independent. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "ref_rel_def"]
def refRel {A B : Type} (R : A → B → Prop) : Ref A → Ref B → Prop
  | .valueArray xs, .valueArray ys => List.Forall₂ R xs ys
  | .byteArray xs, .byteArray ys => xs = ys
  | .thunk m x, .thunk n y => m = n ∧ R x y
  | _, _ => False

/-- Strengthening the contained-value relation preserves related references. -/
theorem refRel_mono {A B : Type} {R S : A → B → Prop} {left : Ref A} {right : Ref B}
    (change : ∀ x y, R x y → S x y) (related : refRel R left right) : refRel S left right := by
  cases left with
  | valueArray xs =>
    cases right with
    | valueArray ys => exact List.Forall₂.imp change related
    | byteArray ys => exact related.elim
    | thunk mode value => exact related.elim
  | byteArray xs =>
    cases right with
    | valueArray ys => exact related.elim
    | byteArray ys => exact related
    | thunk mode value => exact related.elim
  | thunk mode value =>
    cases right with
    | valueArray ys => exact related.elim
    | byteArray ys => exact related.elim
    | thunk mode' value' => exact ⟨related.1, change _ _ related.2⟩

end Flapjack.Compiler.Backend.ClosProps
