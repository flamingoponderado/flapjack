import Flapjack.HolRef

namespace Flapjack.Misc

/-- Literal first-match search with an arbitrary starting offset. Equality is
propositional equality; absence returns none without inspecting the offset. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_def"]
def findIndex {α : Type} [DecidableEq α] (target : α) : List α → Nat → Option Nat
  | [], _ => none
  | head :: tail, offset =>
      if head = target then some offset else findIndex target tail (offset + 1)

end Flapjack.Misc
