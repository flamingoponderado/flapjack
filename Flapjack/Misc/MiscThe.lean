module

public import Flapjack.HolRef

@[expose] public section

namespace Flapjack

/-- CakeML `misc$the` (`cakeml/misc/miscScript.sml:21-24`): the default for
`NONE`, the payload for `SOME`. -/
@[hol "cakeml/misc/miscScript.sml" "the_def"]
def miscThe {α : Type} : α → Option α → α
  | _, some x => x
  | x, none => x

/-- Original `the_nil_eq_cons`: the default list is returned exactly when the
option is `NONE`. -/
@[hol "cakeml/misc/miscScript.sml" "the_nil_eq_cons"]
theorem miscThe_nil_eq_cons {α : Type} (x : Option (List α)) (y : α) (z : List α) :
    miscThe [] x = y :: z ↔ x = some (y :: z) := by
  cases x with
  | none => simp [miscThe]
  | some v => simp [miscThe]

end Flapjack
