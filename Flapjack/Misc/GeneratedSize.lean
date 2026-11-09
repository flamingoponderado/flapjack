module

public import Flapjack.HolRef

@[expose] public section

namespace Flapjack

/-- HOL's size function for an option, with an explicit element measure. -/
@[hol "HOL/src/num/theories/basicSizeScript.sml" "option_size_def"]
def optionSizeHOL {α : Type} (f : α → Nat) : Option α → Nat
  | none => 0
  | some x => 1 + f x

/-- HOL's size function for a pair, with independent component measures. -/
@[hol "HOL/src/num/theories/basicSizeScript.sml" "pair_size_def"]
def pairSizeHOL {α β : Type} (f : α → Nat) (g : β → Nat) : α × β → Nat
  | (x, y) => 1 + (f x + g y)

end Flapjack
