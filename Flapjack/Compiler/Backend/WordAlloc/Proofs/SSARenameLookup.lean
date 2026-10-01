import Flapjack.Compiler.Backend.WordAlloc.SSASetup
namespace Flapjack.Compiler.Backend.WordAlloc
open Flapjack
/-- Flapjack infrastructure proving the full lookup result with a total selector. -/
theorem listNextVarRenameLookup (names : List Nat) (ssa : Spt Nat) (next : Nat)
    (distinct : names.Nodup) :
    let result := listNextVarRename names ssa next
    result.1 = names.map (fun key => (sptLookup key result.2.1).getD 0) ∧
    sptDomain result.2.1 = (fun key => sptDomain ssa key ∨ key ∈ names) ∧
    (∀ key, key ∉ names → sptLookup key result.2.1 = sptLookup key ssa) ∧
    (∀ key, key ∈ names → ∃ value, sptLookup key result.2.1 = some value) := by
  induction names generalizing ssa next with
  | nil => simp [listNextVarRename]
  | cons name names ih =>
    have hnd := List.nodup_cons.mp distinct
    have h := ih (sptInsert name next ssa) (next + 4) hnd.2
    generalize hr : listNextVarRename names (sptInsert name next ssa) (next + 4) = result at h
    rcases result with ⟨outputs, finalMap, finalNext⟩
    simp only at h
    rcases h with ⟨hmap, hdomain, hout, hin⟩
    simp only [listNextVarRename, nextVarRename, hr]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, hmap]
      rw [hout name hnd.1, sptLookup_sptInsert_same]
      rfl
    · funext key
      apply propext
      change sptMem key finalMap ↔ sptMem key ssa ∨ key ∈ name :: names
      have hd := congrFun hdomain key
      change sptMem key finalMap = (sptMem key (sptInsert name next ssa) ∨ key ∈ names) at hd
      rw [hd, sptMem_sptInsert]
      simp only [List.mem_cons]
      simp only [or_assoc, or_left_comm]
    · intro key absent
      have ha : key ≠ name ∧ key ∉ names := by
        simpa only [List.mem_cons, not_or] using absent
      rw [hout key ha.2, sptLookup_sptInsert_ne name key next ssa ha.1]
    · intro key member
      rcases List.mem_cons.mp member with same | tail
      · subst key
        exact ⟨next, by rw [hout name hnd.1, sptLookup_sptInsert_same]⟩
      · exact hin key tail

/-- Flapjack infrastructure: any selector agreeing on SOME yields the same list.
The successful-lookup condition is proved by the preceding result, not assumed.
This discharges the unspecified value of HOL THE NONE. -/
theorem listNextVarRenameSelectorIndependent (names : List Nat) (ssa : Spt Nat)
    (next : Nat) (distinct : names.Nodup) (select : Option Nat → Nat)
    (selectSome : ∀ value, select (some value) = value) :
    (listNextVarRename names ssa next).1 =
      names.map (fun key => select (sptLookup key (listNextVarRename names ssa next).2.1)) := by
  have h := listNextVarRenameLookup names ssa next distinct
  rw [h.1]
  apply List.map_congr_left
  intro key member
  obtain ⟨value, found⟩ := h.2.2.2 key member
  rw [found, selectSome]
  rfl

/-- Full HOL lookup/domain result with ALL_DISTINCT as the sole premise.
`getD 0` renders THE only at successful lookups: the final conjunct establishes
success for every mapped input, and `listNextVarRenameSelectorIndependent`
proves that any selector agreeing on SOME gives the identical result. No claim
about HOL THE NONE or canonical tree well-formedness is required. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "list_next_var_rename_lemma_2"]
theorem listNextVarRenameLemma2 (names : List Nat) (ssa : Spt Nat) (next : Nat) :
    names.Nodup →
    let result := listNextVarRename names ssa next
    result.1 = names.map (fun key => (sptLookup key result.2.1).getD 0) ∧
    sptDomain result.2.1 = (fun key => sptDomain ssa key ∨ key ∈ names) ∧
    (∀ key, key ∉ names → sptLookup key result.2.1 = sptLookup key ssa) ∧
    (∀ key, key ∈ names → ∃ value, sptLookup key result.2.1 = some value) :=
  listNextVarRenameLookup names ssa next
end Flapjack.Compiler.Backend.WordAlloc
