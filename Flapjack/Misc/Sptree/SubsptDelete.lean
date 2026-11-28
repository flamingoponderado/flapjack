module

public import Flapjack.Misc.Sptree.Subspt
public import Flapjack.Misc.SptreeLookup

@[expose] public section

/-!
# `subspt` after deletion

Counterpart of `subspt_delete` from `cakeml/misc/miscScript.sml`, using the
untagged `sptLookup_sptDelete` infrastructure. The `SptreeLookup` import lives
here rather than in the widely imported `Sptree/Subspt.lean`.
-/

namespace Flapjack

/-- Original `subspt_delete`: deleting a key keeps the subtree relation. -/
@[hol "cakeml/misc/miscScript.sml" "subspt_delete"]
theorem subsptDelete {α : Type} (a b : Spt α) (x : Nat) :
    sptSubspt a b → sptSubspt (sptDelete x a) b := by
  intro h k hk
  have hlk := (sptMem_iff_lookup k (sptDelete x a)).mp hk
  obtain ⟨v, hv⟩ := hlk
  have hkx : k ≠ x := by
    intro heq
    subst heq
    rw [sptLookup_sptDelete] at hv
    simp at hv
  have hsame : sptLookup k a = some v := by
    rw [sptLookup_sptDelete] at hv
    rw [if_neg hkx] at hv
    exact hv
  have hk' : sptMem k a := (sptMem_iff_lookup k a).mpr ⟨v, hsame⟩
  obtain ⟨hb, hlook⟩ := h k hk'
  exact ⟨hb, by
    rw [sptLookup_sptDelete, if_neg hkx]
    exact hlook⟩

end Flapjack
