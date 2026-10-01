import Flapjack.HolRef

namespace Flapjack

/-- CakeML `misc$the` (`cakeml/misc/miscScript.sml:21-24`): the default for
`NONE`, the payload for `SOME`. -/
@[hol "cakeml/misc/miscScript.sml" "the_def"]
def miscThe {α : Type} : α → Option α → α
  | _, some x => x
  | x, none => x

end Flapjack
