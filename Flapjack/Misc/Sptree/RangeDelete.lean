module

public import Flapjack.Misc.Sptree.Range
public import Flapjack.Misc.SptreeLookup

@[expose] public section

/-!
# `range_delete`

Counterpart of `range_delete` from `cakeml/misc/miscScript.sml`: deleting a key
from a sparse tree can only shrink the set of stored values.

This module sits beside `Sptree.Range` rather than inside it because it needs the
`lookup_delete` characterisation from `Misc.SptreeLookup`, whose import would
change the simp set of the modules that use `Sptree.Range` directly.
-/

namespace Flapjack

/-- Original `range_delete`: deleting a key keeps the range inside the old one. -/
@[hol "cakeml/misc/miscScript.sml" "range_delete"]
theorem rangeDelete {α : Type} (h : Nat) (v : Spt α) :
    sptRange (sptDelete h v) ⊆ sptRange v := by
  intro w hw
  obtain ⟨n, hn⟩ := hw
  rw [sptLookup_sptDelete] at hn
  by_cases heq : n = h
  · rw [if_pos heq] at hn
    simp at hn
  · rw [if_neg heq] at hn
    exact ⟨n, hn⟩

end Flapjack
