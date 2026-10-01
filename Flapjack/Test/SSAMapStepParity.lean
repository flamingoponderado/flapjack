import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapStep

namespace Flapjack.Test.SSAMapStepParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc

private theorem singleValid (next value : Nat) (nonphysical : ¬ isPhyVar value)
    (bound : value < next) : ssaMapOK next (.ls value) := by
  intro key foundValue found
  simp only [sptLookup] at found
  split at found
  · cases found
    exact ⟨nonphysical, bound⟩
  · contradiction

private theorem physicalInvalid (next : Nat) : ¬ ssaMapOK next (.ls 2) := by
  intro valid
  exact (valid 0 2 rfl).1 (by decide)

example (next : Nat) (ssa : Spt Nat) (valid : ssaMapOK next ssa) :
    ssaMapOK (next + 2) ssa := ssaMapOKLem next ssa valid

example : ssaMapOK 0 .ln ∧ ssaMapOK (0 + 2) .ln := by
  simp [ssaMapOK, sptLookup]
example : ssaMapOK 8 (.ls 7) ∧ ssaMapOK (8 + 2) (.ls 7) := by
  have valid := singleValid 8 7 (by decide) (by decide)
  exact ⟨valid, ssaMapOKLem 8 (.ls 7) valid⟩
example : ¬ ssaMapOK 7 (.ls 7) ∧ ssaMapOK (7 + 2) (.ls 7) := by
  refine ⟨?_, singleValid 9 7 (by decide) (by decide)⟩
  intro valid
  exact Nat.lt_irrefl 7 (valid 0 7 rfl).2
example : ¬ ssaMapOK 100 (.ls 2) ∧ ¬ ssaMapOK (100 + 2) (.ls 2) :=
  ⟨physicalInvalid 100, physicalInvalid 102⟩
example : ssaMapOK 0 (.bn .ln .ln) ∧ ssaMapOK (0 + 2) (.bn .ln .ln) := by
  have valid : ssaMapOK 0 (.bn .ln .ln) := by
    intro key value found
    simp [sptLookup] at found
  exact ⟨valid, ssaMapOKLem 0 _ valid⟩
example : ssaMapOK 18446744073709551624 (.ls 18446744073709551621) ∧
    ssaMapOK (18446744073709551624 + 2) (.ls 18446744073709551621) := by
  have valid := singleValid 18446744073709551624 18446744073709551621
    (by decide) (by decide)
  exact ⟨valid, ssaMapOKLem _ _ valid⟩

end Flapjack.Test.SSAMapStepParity
