import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapPreservation
namespace Flapjack.Test.SSAMapPreservationParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc
private theorem emptyOK (n : Nat) : ssaMapOK n .ln := by simp [ssaMapOK, sptLookup]
private theorem invalidOK (n : Nat) : ssaMapOK n (.bn .ln .ln) := by
  intro x y h
  simp [sptLookup] at h
private theorem leafOK (n v : Nat) (hv : ¬ isPhyVar v ∧ v < n) : ssaMapOK n (.ls v) := by
  intro x y h
  simp only [sptLookup] at h
  split at h
  · cases h; exact hv
  · contradiction
private theorem branchOK : ssaMapOK 8 (.bs (.ls 1) 3 (.ls 7)) := by
  intro x y h
  simp only [sptLookup] at h
  split at h
  · cases h; decide
  · split at h <;> split at h <;> (first | contradiction | (cases h; decide))
-- Original mi_empty=T; full theorem application.
example : ssaMapOK 8 (sptInter (.ln : Spt Nat) (.ls true : Spt Bool)) :=
  ssaMapOKInter 8 (.ln) (.ls true : Spt Bool) (emptyOK _)
-- Original mi_retain_alloc=T; full theorem application.
example : ssaMapOK 8 (sptInter (.ls 1 : Spt Nat) (.ls true : Spt Bool)) :=
  ssaMapOKInter 8 (.ls 1) (.ls true : Spt Bool) (leafOK _ _ (by decide))
-- Original mi_retain_stack=T; full theorem application.
example : ssaMapOK 8 (sptInter (.ls 7 : Spt Nat) (.ls false : Spt Bool)) :=
  ssaMapOKInter 8 (.ls 7) (.ls false : Spt Bool) (leafOK _ _ (by decide))
-- Original mi_drop=T; full theorem application.
example : ssaMapOK 8 (sptInter (.ls 7 : Spt Nat) (.ln : Spt Bool)) :=
  ssaMapOKInter 8 (.ls 7) (.ln : Spt Bool) (leafOK _ _ (by decide))
-- Original mi_invalid=T; full theorem application.
example : ssaMapOK 8 (sptInter (.bn .ln .ln : Spt Nat) (.bs .ln true .ln : Spt Bool)) :=
  ssaMapOKInter 8 (.bn .ln .ln) (.bs .ln true .ln : Spt Bool) (invalidOK _)
-- Original mi_branch=T; full theorem application.
example : ssaMapOK 8 (sptInter (.bs (.ls 1) 3 (.ls 7) : Spt Nat) (.bs .ln true (.ls false) : Spt Bool)) :=
  ssaMapOKInter 8 (.bs (.ls 1) 3 (.ls 7)) (.bs .ln true (.ls false) : Spt Bool) (branchOK)
-- Original mi_huge=T; full theorem application.
example : ssaMapOK 1000000000000000000000000000004 (sptInter (.ls 1000000000000000000000000000003 : Spt Nat) (.ls true : Spt Bool)) :=
  ssaMapOKInter 1000000000000000000000000000004 (.ls 1000000000000000000000000000003) (.ls true : Spt Bool) (leafOK _ _ (by decide))
-- Original ms_empty=T; full theorem application.
example : ssaMapOK 8 (sptInsert 0 1 (.ln)) :=
  ssaMapOKInsert 8 (.ln) 0 1 ⟨emptyOK _, by decide, by decide⟩
-- Original ms_stack=T; full theorem application.
example : ssaMapOK 8 (sptInsert 2 7 (.ln)) :=
  ssaMapOKInsert 8 (.ln) 2 7 ⟨emptyOK _, by decide, by decide⟩
-- Original ms_overwrite=T; full theorem application.
example : ssaMapOK 8 (sptInsert 0 3 (.ls 1)) :=
  ssaMapOKInsert 8 (.ls 1) 0 3 ⟨leafOK _ _ (by decide), by decide, by decide⟩
-- Original ms_extend=T; full theorem application.
example : ssaMapOK 8 (sptInsert 2 5 (.ls 7)) :=
  ssaMapOKInsert 8 (.ls 7) 2 5 ⟨leafOK _ _ (by decide), by decide, by decide⟩
-- Original ms_invalid=T; full theorem application.
example : ssaMapOK 8 (sptInsert 2 1 (.bn .ln .ln)) :=
  ssaMapOKInsert 8 (.bn .ln .ln) 2 1 ⟨invalidOK _, by decide, by decide⟩
-- Original ms_huge=T; full theorem application.
example : ssaMapOK 1000000000000000000000000000004 (sptInsert 1000000000000000000000000000000 1000000000000000000000000000003 (.ls 7)) :=
  ssaMapOKInsert 1000000000000000000000000000004 (.ls 7) 1000000000000000000000000000000 1000000000000000000000000000003 ⟨leafOK _ _ (by decide), by decide, by decide⟩
example : ¬ (¬ isPhyVar 2) := by decide
example : ¬ (8 < (8 : Nat)) := by decide
end Flapjack.Test.SSAMapPreservationParity
