module

public import Flapjack.HolRef
public import Mathlib.Data.List.Basic

@[expose] public section

namespace Flapjack

/-- Exact HOL `update_resize_def` (`miscScript.sml:594-601`): overwrite index
`n`, first extending the list with `default` entries when `n` is out of range.
HOL's `n * 2 + 1 - LENGTH ls` is truncated subtraction on `num`, matching
Lean's `Nat` subtraction. -/
@[hol "cakeml/misc/miscScript.sml" "update_resize_def"]
def updateResize {α : Type} (ls : List α) (default : α) (v : α) (n : Nat) : List α :=
  if n < ls.length then ls.set n v
  else (ls ++ List.replicate (n * 2 + 1 - ls.length) default).set n v

end Flapjack
