import Flapjack.Compiler.Backend.StackRawCall.Proofs.StateOk
namespace Flapjack.Test.StackRawCallStateOkParity
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall
example (code : Spt (HolProg 64)) : stateOk .ln code := stateOk_empty code
private theorem entry (size : Nat) :
    stateOk (sptInsert 7 size .ln)
      (sptInsert 7 (.seq (.stackAlloc size) .skip : HolProg 64) .ln) := by
  intro n v h
  by_cases hn : n = 7
  · subst n
    rw [sptLookup_sptInsert_same] at h
    cases h
    exact ⟨.skip, sptLookup_sptInsert_same _ _ _⟩
  · rw [sptLookup_sptInsert_ne _ _ _ _ hn] at h
    simp [sptLookup] at h
example : stateOk (sptInsert 7 4 .ln)
    (sptInsert 7 (.seq (.stackAlloc 4) .skip : HolProg 64) .ln) := entry 4
example : stateOk (sptInsert 7 0 .ln)
    (sptInsert 7 (.seq (.stackAlloc 0) .skip : HolProg 64) .ln) := entry 0
example : ¬stateOk (sptInsert 7 4 .ln)
    (sptInsert 7 (.stackAlloc 4 : HolProg 64) .ln) := by
  intro h
  obtain ⟨body, hb⟩ := h 7 4 (sptLookup_sptInsert_same _ _ _)
  rw [sptLookup_sptInsert_same] at hb
  cases hb
example : ¬stateOk (sptInsert 7 4 .ln)
    (sptInsert 7 (.seq (.stackAlloc 6) .skip : HolProg 64) .ln) := by
  intro h
  obtain ⟨body, hb⟩ := h 7 4 (sptLookup_sptInsert_same _ _ _)
  rw [sptLookup_sptInsert_same] at hb
  cases hb
end Flapjack.Test.StackRawCallStateOkParity
