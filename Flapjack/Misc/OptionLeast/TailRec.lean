module

public import Flapjack.Misc.OptionLeast.TailCall

@[expose] public section

/-! A total model satisfying HOL's tail-recursive specification. -/
namespace Flapjack.HOL

/-- Execute tail calls, recording divergence with `none`. -/
def tailRecPartial {α β : Type} (f : α → Sum α β) (x : α) : Option β :=
  match f x with
  | .inl next => tailRecPartial f next
  | .inr result => some result
partial_fixpoint

/-- A selected solution to the HOL tail-recursion equation. HOL types are
    nonempty; the explicit Lean instance supplies the divergent-case choice.
    This model is not tagged as the HOL specification, whose choice of solution
    is unspecified on diverging inputs. -/
noncomputable def tailRecModel {α β : Type} [Nonempty β] (f : α → Sum α β) (x : α) : β :=
  (tailRecPartial f x).getD (Classical.choice inferInstance)

/-- The selected solution satisfies the complete tail-recursion equation,
    including at diverging inputs. -/
theorem tailRecModelEq {α β : Type} [Nonempty β] (f : α → Sum α β) (x : α) :
    tailRecModel f x = tailCall f (tailRecModel f) x := by
  unfold tailRecModel tailCall
  rw [tailRecPartial.eq_1]
  cases f x <;> rfl

/-- A terminating partial execution fixes the total model's result. -/
theorem tailRecModelOfSome {α β : Type} [Nonempty β] (f : α → Sum α β)
    (x : α) (result : β) (h : tailRecPartial f x = some result) :
    tailRecModel f x = result := by
  simp [tailRecModel, h]

end Flapjack.HOL
