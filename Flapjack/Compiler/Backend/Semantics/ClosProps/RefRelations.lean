module

public import Flapjack.Compiler.Backend.Semantics.ClosSem
public import Mathlib.Data.List.Forall2

@[expose] public section

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

/-- Original `ref_rel_simp`: the introduction equations of `refRel` for the
    three reference constructors. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "ref_rel_simp"]
theorem refRel_simp {A B : Type} (R : A → B → Prop) :
    (∀ (vs : List A) (y : Ref B),
        refRel R (.valueArray vs) y ↔ ∃ ws, y = .valueArray ws ∧ List.Forall₂ R vs ws) ∧
    (∀ (bs : List (BitVec 8)) (y : Ref B),
        refRel R (.byteArray bs) y ↔ y = .byteArray bs) ∧
    (∀ (m : AstHOL.ThunkMode) (a : A) (y : Ref B),
        refRel R (.thunk m a) y ↔ ∃ b, y = .thunk m b ∧ R a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro vs y
    cases y
    all_goals simp [refRel]
  · intro bs y
    cases y
    all_goals simp [refRel, eq_comm]
  · intro m a y
    cases y
    all_goals simp [refRel, eq_comm]

end Flapjack.Compiler.Backend.ClosProps
