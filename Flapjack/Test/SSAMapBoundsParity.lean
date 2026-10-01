import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapBounds

namespace Flapjack.Test.SSAMapBoundsParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc

private theorem singleValid (next value : Nat) (nonphysical : ¬ isPhyVar value)
    (bound : value < next) : ssaMapOK next (.ls value) := by
  intro key foundValue found
  simp only [sptLookup] at found
  split at found
  · cases found
    exact ⟨nonphysical, bound⟩
  · contradiction

private theorem singlePhysical (next value : Nat) (physical : isPhyVar value) :
    ¬ ssaMapOK next (.ls value) := by
  intro valid
  exact (valid 0 value rfl).1 physical

-- Identical whole predicate pairs to the fresh original observations.
example : ssaMapOK 0 .ln ∧ ssaMapOK 17 .ln := by simp [ssaMapOK, sptLookup]
example : ssaMapOK 8 (.ls 7) ∧ ssaMapOK 12 (.ls 7) := by
  have valid := singleValid 8 7 (by decide) (by decide)
  exact ⟨valid, ssaMapOKMore 8 (.ls 7) 12 ⟨valid, by decide⟩⟩
example : ssaMapOK 8 (.ls 7) ∧ ssaMapOK 8 (.ls 7) := by
  have valid := singleValid 8 7 (by decide) (by decide)
  exact ⟨valid, ssaMapOKMore 8 (.ls 7) 8 ⟨valid, Nat.le_refl _⟩⟩
example : ¬ ssaMapOK 7 (.ls 7) ∧ ssaMapOK 8 (.ls 7) := by
  refine ⟨?_, singleValid 8 7 (by decide) (by decide)⟩
  intro valid
  exact Nat.lt_irrefl 7 (valid 0 7 rfl).2
example : ¬ ssaMapOK 100 (.ls 2) ∧ ¬ ssaMapOK 200 (.ls 2) :=
  ⟨singlePhysical 100 2 (by decide), singlePhysical 200 2 (by decide)⟩
example : ssaMapOK 0 (.bn .ln .ln) ∧ ssaMapOK 1 (.bn .ln .ln) := by
  have valid : ssaMapOK 0 (.bn .ln .ln) := by intro key value found; simp [sptLookup] at found
  exact ⟨valid, ssaMapOKMore _ _ 1 ⟨valid, by decide⟩⟩
example : ¬ ssaMapOK 18446744073709551624 (.ls 18446744073709551620) ∧
    ¬ ssaMapOK 18446744073709551632 (.ls 18446744073709551620) :=
  ⟨singlePhysical _ _ (by decide), singlePhysical _ _ (by decide)⟩
example : ssaMapOK 18446744073709551624 (.ls 18446744073709551621) ∧
    ssaMapOK 18446744073709551632 (.ls 18446744073709551621) := by
  have valid := singleValid 18446744073709551624 18446744073709551621 (by decide) (by decide)
  exact ⟨valid, ssaMapOKMore _ _ _ ⟨valid, by decide⟩⟩
example : sptInsert 0 7 (.ls 2) = .ls 7 := by decide +kernel
example : ssaMapOK 8 (sptInsert 0 7 (.ls 2)) ∧ ssaMapOK 12 (sptInsert 0 7 (.ls 2)) := by
  have valid : ssaMapOK 8 (sptInsert 0 7 (.ls 2)) := by
    simpa only [sptInsert, Nat.reduceEqDiff, ↓reduceIte] using
      singleValid 8 7 (by decide) (by decide)
  exact ⟨valid, ssaMapOKMore _ _ _ ⟨valid, by decide⟩⟩
-- Actual full theorem application retains arbitrary maps and both bounds.
example (next nextOut : Nat) (ssa : Spt Nat) (valid : ssaMapOK next ssa)
    (bound : next ≤ nextOut) : ssaMapOK nextOut ssa :=
  ssaMapOKMore next ssa nextOut ⟨valid, bound⟩

end Flapjack.Test.SSAMapBoundsParity
