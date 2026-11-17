module

public import Flapjack.HolRef

@[expose] public section

/-! First-order terms used by HOL's triangular unification development. -/
namespace Flapjack.HOL.Unification

@[hol "HOL/examples/algorithms/unification/triangular/first-order/termScript.sml" "term"]
inductive Term (α : Type) where
  | var : Nat → Term α
  | pair : Term α → Term α → Term α
  | const : α → Term α
  deriving DecidableEq, Repr

@[hol "HOL/examples/algorithms/unification/triangular/first-order/termScript.sml" "pair_count_def"]
def pairCount {α : Type} : Term α → Nat
  | .var _ => 0
  | .pair left right => 1 + pairCount left + pairCount right
  | .const _ => 0

@[hol "HOL/examples/algorithms/unification/triangular/first-order/termScript.sml" "vars_def"]
def vars {α : Type} : Term α → Nat → Prop
  | .var x => fun n => n = x
  | .pair left right => fun n => vars left n ∨ vars right n
  | .const _ => fun _ => False

end Flapjack.HOL.Unification
