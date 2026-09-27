import Flapjack.HolRef
import Flapjack.PanToCrepMaxList

/-!
Exact port of HOL `misc$FOLDR_MAX_0_MAX_LIST`
(`cakeml/misc/miscScript.sml:630`):

    Theorem FOLDR_MAX_0_MAX_LIST:
      ∀ls. FOLDR MAX 0 ls = MAX_LIST ls

`MAX_LIST` is HOL's `rich_list$MAX_LIST` (`MAX_LIST [] = 0`,
`MAX_LIST (h::t) = MAX h (MAX_LIST t)`), rendered here by the executable
`Flapjack.maxList` (see `Flapjack/PanToCrepMaxList.lean`).  HOL `FOLDR MAX 0`
is `List.foldr max 0` and HOL `MAX` is `max` on `num`.
-/

namespace Flapjack

@[hol "cakeml/misc/miscScript.sml" "FOLDR_MAX_0_MAX_LIST"]
theorem foldrMaxZeroMaxListHOL (values : List Nat) :
    values.foldr max 0 = maxList values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.foldr_cons, maxList, ih]

end Flapjack
