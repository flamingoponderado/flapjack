module

public import Flapjack.Pancake.CrepToLoop
public import Flapjack.Misc.Sptree

@[expose] public section

/-!
# First-match lookup for numeric association lists

The register allocator's extraction, move-table, tag-decoding and spill-cost
proofs all relate `lookupNatInfo` to the external Sptree `ALOOKUP` rendering
`sptAListLookup`. This is Flapjack proof infrastructure; there is no separately
named HOL original.
-/

namespace Flapjack

/-- Flapjack infrastructure: first-match association-list lookup agrees with the
external Sptree `ALOOKUP` rendering. No separately named HOL original. -/
theorem lookup_first {α : Type} (key : Nat) (entries : NatInfoMap α) :
    lookupNatInfo key entries = sptAListLookup key entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨other, value⟩ := entry
    simp only [lookupNatInfo, sptAListLookup, Bool.beq_eq_decide_eq]
    by_cases equal : key = other
    · subst other
      simp
    · simp [equal, Ne.symm equal, ih]

end Flapjack
