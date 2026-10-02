import Flapjack.Compiler.Backend.LabToTarget.LabsDomain

namespace Flapjack.Test.LabToTargetLabsDomainParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget

/-- Original HOL probe observations, using the actual nested tree operations. -/
private def old : Spt (Spt Nat) := sptInsert 1 (sptInsert 2 99 .ln) .ln
private def added : Spt (Spt Nat) := sptInsert 3 (sptInsert 4 5 .ln) old

example : (1,2) ∉ labsDomain (.ln : Spt (Spt Nat)) := by
  change ¬(labLookup 1 2 (.ln : Spt (Spt Nat)) ≠ none)
  decide +kernel
example : (1,2) ∈ labsDomain old := by
  change (labLookup 1 2 old ≠ none)
  decide +kernel
example : (1,3) ∉ labsDomain old := by
  change ¬(labLookup 1 3 old ≠ none)
  decide +kernel
example : (3,2) ∉ labsDomain old := by
  change ¬(labLookup 3 2 old ≠ none)
  decide +kernel
example : (1,2) ∈ labsDomain added := by
  change (labLookup 1 2 added ≠ none)
  decide +kernel
example : (3,4) ∈ labsDomain added := by
  change (labLookup 3 4 added ≠ none)
  decide +kernel

-- Full generic consumers retain arbitrary values and the original guard.
example {α : Type} (k : Nat) (s : Spt α) (labs : Spt (Spt α))
    (h : ¬ sptDomain labs k) : labsDomain (sptInsert k s labs) =
    (fun n => (k,n)) '' sptDomain s ∪ labsDomain labs := labsDomain_insert k s labs h

end Flapjack.Test.LabToTargetLabsDomainParity
