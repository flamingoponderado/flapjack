import Flapjack.Misc.Sptree

/-!
Regression pinning `Misc.Sptree` (the exact `spt`/`num_set` carrier) against the
direct HOL oracle `scripts/hol-probes/num_set_spt_probe.out`.
-/

namespace Flapjack.Test.SptreeParity

open Flapjack

/-- The empty `num_set`. -/
private def emptyTree : NumSet := .ln

/-- One element (`0`) inserted into the empty set. -/
private def zeroInserted : NumSet := sptInsert 0 () emptyTree

/-- Two elements (`0` then `1`) inserted into the empty set. -/
private def twoInserted : NumSet := sptInsert 1 () zeroInserted

/-- Three elements (`0`, `1`, `2`). -/
private def threeInserted : NumSet := sptInsert 2 () twoInserted

/-- `0` and `5`. -/
private def fiveInserted : NumSet := sptInsert 5 () zeroInserted

/-- `0`, `1`, `2`, `3`. -/
private def fourInserted : NumSet := sptInsert 3 () threeInserted

-- 1. `lookup_ln`
example : sptLookup 0 emptyTree = none := by simp [emptyTree]
-- 2. `insert0`
example : sptInsert 0 () emptyTree = .ls () := by simp [emptyTree]
-- 3. `lookup_ins0`
example : sptLookup 0 zeroInserted = some () := by simp [zeroInserted, emptyTree, sptLookup]
-- 4. `lookup_ins1_0`
example : sptLookup 0 twoInserted = some () := by simp [twoInserted, zeroInserted, emptyTree, sptInsert, sptLookup]
-- 5. `lookup_ins_other`
example : sptLookup 5 (sptInsert 2 () emptyTree) = none := by simp [emptyTree, sptInsert, sptLookup]
-- 6. `insert1_shape`
example : sptInsert 1 () emptyTree = .bn .ln (.ls ()) := by simp [emptyTree, sptInsert]
-- 7. `insert2_shape`
example : sptInsert 2 () emptyTree = .bn (.ls ()) .ln := by simp [emptyTree, sptInsert]
-- 8. `wf_ins`
example : sptWf twoInserted = true := by simp [twoInserted, zeroInserted, emptyTree, sptInsert, sptIsEmpty, sptWf]
-- 9. `isempty_ln`
example : sptIsEmpty emptyTree = true := by simp [emptyTree, sptIsEmpty]
-- 10. `isempty_ins`
example : sptIsEmpty zeroInserted = false := by simp [zeroInserted, emptyTree, sptIsEmpty]
-- 11. `insert_ovw`
example : sptLookup 0 (sptInsert 0 () zeroInserted) = some () := by simp [zeroInserted, emptyTree, sptInsert, sptLookup]

-- Enumeration order rows from `scripts/hol-probes/num_set_to_alist_probe.out`.
-- 12. `toalist_ln`
example : sptToAList emptyTree = [] := by simp [emptyTree, sptToAList, sptFoldi]
-- 13. `toalist_zero`
example : sptToAList zeroInserted = [(0, ())] := by simp [zeroInserted, emptyTree, sptToAList, sptFoldi]
-- 14. `toalist_two`
example : sptToAList twoInserted = [(1, ()), (0, ())] := by simp [twoInserted, zeroInserted, emptyTree, sptInsert, sptToAList, sptFoldi, lrNext]
-- 15. `toalist_three`
example : sptToAList threeInserted = [(1, ()), (0, ()), (2, ())] := by simp [threeInserted, twoInserted, zeroInserted, emptyTree, sptInsert, sptToAList, sptFoldi, lrNext]
-- 16. `toalist_five`
example : sptToAList fiveInserted = [(5, ()), (0, ())] := by simp [fiveInserted, zeroInserted, emptyTree, sptInsert, sptToAList, sptFoldi, lrNext]
-- 17. `toalist_four`
example : sptToAList fourInserted = [(3, ()), (1, ()), (0, ()), (2, ())] := by simp [fourInserted, threeInserted, twoInserted, zeroInserted, emptyTree, sptInsert, sptToAList, sptFoldi, lrNext]

/-- Executable mirror of the oracle rows for `#guard`. -/
private def sptreeGuard : Bool :=
  (sptLookup 0 emptyTree == none) &&
    (sptInsert 0 () emptyTree == .ls ()) &&
    (sptLookup 0 zeroInserted == some ()) &&
    (sptLookup 0 twoInserted == some ()) &&
    (sptLookup 5 (sptInsert 2 () emptyTree) == none) &&
    (sptInsert 1 () emptyTree == .bn .ln (.ls ())) &&
    (sptInsert 2 () emptyTree == .bn (.ls ()) .ln) &&
    (sptWf twoInserted == true) &&
    (sptIsEmpty emptyTree == true) &&
    (sptIsEmpty zeroInserted == false) &&
    (sptLookup 0 (sptInsert 0 () zeroInserted) == some ()) &&
      (sptToAList emptyTree == []) &&
      (sptToAList zeroInserted == [(0, ())]) &&
      (sptToAList twoInserted == [(1, ()), (0, ())]) &&
      (sptToAList threeInserted == [(1, ()), (0, ()), (2, ())]) &&
      (sptToAList fiveInserted == [(5, ()), (0, ())]) &&
      (sptToAList fourInserted == [(3, ()), (1, ()), (0, ()), (2, ())])

#eval sptreeGuard
#guard sptreeGuard

/-- The oracle lookup/insert lemma for key `0` also holds for an arbitrary tree. -/
example (value : Unit) (tree : NumSet) : sptLookup 0 (sptInsert 0 value tree) = some value :=
  sptLookup_sptInsert_zero value tree

/-- `domain_lookup` (HOL sptree `:620`) turns any lookup witness into a
    membership witness. -/
example (v : Unit) (h : sptLookup 2 threeInserted = some v) : sptMem 2 threeInserted :=
  (sptMem_iff_lookup 2 threeInserted).mpr ⟨v, h⟩

/-- Inserting key `0` makes it a domain member (`domain_lookup` in the other
    direction). -/
example (value : Unit) : sptMem 0 (sptInsert 0 value (Spt.ln : NumSet)) :=
  (sptMem_iff_lookup 0 _).mpr ⟨value, sptLookup_sptInsert_zero value .ln⟩

/-- The empty tree has empty domain. -/
example : ¬ sptMem 7 (Spt.ln : NumSet) := sptMem_ln 7

/-- The `BN` `domain_def` clause on the exact carrier. -/
example : sptMem 1 (.bn (.ls () : NumSet) .ln) ↔
    (∃ m, sptMem m (.ls () : NumSet) ∧ 1 = 2 * m + 2) ∨
      (∃ m, sptMem m (.ln : NumSet) ∧ 1 = 2 * m + 1) :=
  sptMem_bn (.ls () : NumSet) .ln 1

/-- The `BS` `domain_def` clause on the exact carrier. -/
example : sptMem 0 (.bs .ln () (.ln : NumSet)) ↔
    0 = 0 ∨ (∃ m, sptMem m (.ln : NumSet) ∧ 0 = 2 * m + 2) ∨
      (∃ m, sptMem m (.ln : NumSet) ∧ 0 = 2 * m + 1) :=
  sptMem_bs .ln () .ln 0

def runChecks : IO Bool := do
  IO.println "PASS exact spt/num_set carrier lookup/insert/wf and toAList enumeration order match the 17 oracle rows"
  pure sptreeGuard

end Flapjack.Test.SptreeParity