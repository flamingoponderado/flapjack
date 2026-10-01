import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMap
namespace Flapjack.Test.SSAMapParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc
-- Identical original quantified predicate observations; kernel simplification.
example : ssaMapOK 0 .ln := by simp [ssaMapOK, sptLookup]
example : ssaMapOK 8 (.ls 7) := by
  intro x y h
  simp only [sptLookup] at h
  split at h
  · cases h; decide
  · contradiction
example : ¬ ssaMapOK 7 (.ls 7) := by
  intro h
  have hy := h 0 7 (by rfl)
  exact (by decide : ¬ (7 < 7)) hy.2
example : ¬ ssaMapOK 100 (.ls 2) := by
  intro h
  have hy := h 0 2 (by rfl)
  exact hy.1 (by decide)
example : ssaMapOK 0 (.bn .ln .ln) := by
  intro x y h
  simp [sptLookup] at h
end Flapjack.Test.SSAMapParity
