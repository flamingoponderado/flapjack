module

public import Flapjack.HolRef

@[expose] public section

/-! HOL's tail-call step. -/
namespace Flapjack.HOL

@[hol "HOL/src/num/theories/WhileScript.sml" "TAILCALL_def"]
def tailCall {α β γ : Type} (f : α → Sum β γ) (k : β → γ) (x : α) : γ :=
  match f x with
  | .inl next => k next
  | .inr result => result

end Flapjack.HOL
