module

public import Flapjack.Misc.Sptree.Subspt
public import Mathlib.Data.Set.Defs

@[expose] public section

namespace Flapjack

/-- A sparse subtree has no domain key absent from the containing tree. -/
@[hol "cakeml/misc/miscScript.sml" "subspt_domain_SUBSET"]
theorem sptSubspt_domainSubset {α : Type} (first second : Spt α)
    (relation : sptSubspt first second) : Set.Subset (sptDomain first) (sptDomain second) := by
  intro key member
  exact (relation key member).1

end Flapjack
