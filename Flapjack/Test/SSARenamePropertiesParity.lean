import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameProperties
namespace Flapjack.Test.SSARenamePropertiesParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc
-- These claims apply the full public theorem, including final map correctness.
def claims (names : List Nat) (ssa : Spt Nat) (next : Nat) : Prop :=
  let result := listNextVarRename names ssa next
  next ≤ result.2.2 ∧ (isAllocVar next → isAllocVar result.2.2) ∧
    (isStackVar next → isStackVar result.2.2) ∧ ssaMapOK result.2.2 result.2.1
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
-- Original rp_empty_alloc: (1,T).
example : claims [] .ln 1 :=
  listNextVarRenameProps [] .ln 1 _ _ _ rfl ⟨Or.inl (by decide), emptyOK 1⟩
example : (listNextVarRename [] .ln 1).2.2 = 1 := by decide +kernel
-- Original rp_empty_stack: (3,T).
example : claims [] .ln 3 :=
  listNextVarRenameProps [] .ln 3 _ _ _ rfl ⟨Or.inr (by decide), emptyOK 3⟩
example : (listNextVarRename [] .ln 3).2.2 = 3 := by decide +kernel
-- Original rp_alloc_duplicates: (13,T).
example : claims [9,9,2] .ln 1 :=
  listNextVarRenameProps [9,9,2] .ln 1 _ _ _ rfl ⟨Or.inl (by decide), emptyOK 1⟩
example : (listNextVarRename [9,9,2] .ln 1).2.2 = 13 := by decide +kernel
-- Original rp_stack_duplicates: (15,T).
example : claims [9,9,2] .ln 3 :=
  listNextVarRenameProps [9,9,2] .ln 3 _ _ _ rfl ⟨Or.inr (by decide), emptyOK 3⟩
example : (listNextVarRename [9,9,2] .ln 3).2.2 = 15 := by decide +kernel
-- Original rp_existing: (17,T).
example : claims [9,1] (.ls 7) 9 :=
  listNextVarRenameProps [9,1] (.ls 7) 9 _ _ _ rfl ⟨Or.inl (by decide), existingOK⟩
example : (listNextVarRename [9,1] (.ls 7) 9).2.2 = 17 := by decide +kernel
-- Original rp_overwrite: (17,T).
example : claims [0,0] (.ls 7) 9 :=
  listNextVarRenameProps [0,0] (.ls 7) 9 _ _ _ rfl ⟨Or.inl (by decide), existingOK⟩
example : (listNextVarRename [0,0] (.ls 7) 9).2.2 = 17 := by decide +kernel
-- Original rp_invalid: (9,T).
example : claims [2,2] (.bn .ln .ln) 1 :=
  listNextVarRenameProps [2,2] (.bn .ln .ln) 1 _ _ _ rfl ⟨Or.inl (by decide), invalidOK⟩
example : (listNextVarRename [2,2] (.bn .ln .ln) 1).2.2 = 9 := by decide +kernel
-- Original rp_huge: (1000000000000000000000000000013,T).
example : claims [1000000000000000000000000000000,0,0] .ln 1000000000000000000000000000001 :=
  listNextVarRenameProps [1000000000000000000000000000000,0,0] .ln 1000000000000000000000000000001 _ _ _ rfl ⟨Or.inl (by decide), emptyOK 1000000000000000000000000000001⟩
example : (listNextVarRename [1000000000000000000000000000000,0,0] .ln 1000000000000000000000000000001).2.2 = 1000000000000000000000000000013 := by decide +kernel
end Flapjack.Test.SSARenamePropertiesParity
