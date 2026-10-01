import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapExtend
namespace Flapjack.Test.SSAMapExtendParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc
private theorem emptyOK (next : Nat) : ssaMapOK next .ln := by
  simp [ssaMapOK, sptLookup]
private theorem existingOK : ssaMapOK 9 (.ls 7) := by
  intro x y h
  simp only [sptLookup] at h
  split at h
  · cases h; decide
  · contradiction
private theorem invalidOK : ssaMapOK 1 (.bn .ln .ln) := by
  intro x y h
  simp [sptLookup] at h
-- Original se_empty_alloc=T: actual complete public theorem application.
example : ssaMapOK (1+4) (sptInsert 0 1 .ln) :=
  ssaMapOKExtend 1 .ln 0 ⟨emptyOK 1, by decide⟩
-- Original se_empty_stack=T: actual complete public theorem application.
example : ssaMapOK (3+4) (sptInsert 0 3 .ln) :=
  ssaMapOKExtend 3 .ln 0 ⟨emptyOK 3, by decide⟩
-- Original se_existing=T: actual complete public theorem application.
example : ssaMapOK (9+4) (sptInsert 9 9 (.ls 7)) :=
  ssaMapOKExtend 9 (.ls 7) 9 ⟨existingOK, by decide⟩
-- Original se_overwrite=T: actual complete public theorem application.
example : ssaMapOK (9+4) (sptInsert 0 9 (.ls 7)) :=
  ssaMapOKExtend 9 (.ls 7) 0 ⟨existingOK, by decide⟩
-- Original se_invalid=T: actual complete public theorem application.
example : ssaMapOK (1+4) (sptInsert 2 1 (.bn .ln .ln)) :=
  ssaMapOKExtend 1 (.bn .ln .ln) 2 ⟨invalidOK, by decide⟩
-- Original se_huge_alloc=T: actual complete public theorem application.
example : ssaMapOK (1000000000000000000000000000001+4) (sptInsert 1000000000000000000000000000000 1000000000000000000000000000001 .ln) :=
  ssaMapOKExtend 1000000000000000000000000000001 .ln 1000000000000000000000000000000 ⟨emptyOK _, by decide⟩
-- Original se_huge_stack=T: actual complete public theorem application.
example : ssaMapOK (1000000000000000000000000000003+4) (sptInsert 0 1000000000000000000000000000003 .ln) :=
  ssaMapOKExtend 1000000000000000000000000000003 .ln 0 ⟨emptyOK _, by decide⟩
-- Original false-premise sentinels.
example : ¬ (¬ isPhyVar 2) := by decide
example : ¬ ssaMapOK 7 (.ls 7) := by
  intro h
  exact (by decide : ¬ (7 < 7)) (h 0 7 rfl).2
end Flapjack.Test.SSAMapExtendParity
