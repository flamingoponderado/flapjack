import Flapjack.FiniteMap.Basic

/-!
Regression checks for the external HOL theorem
`HOL/src/finite_maps/finite_mapScript.sml:2960`,
`FUPDATE_LIST_APPEND_COMMUTES`, used at
`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1001,1197`.

The committed direct HOL observation is
`scripts/hol-probes/fupdate_list_append_commutes_probe.out`. The general Lean
port is intentionally untagged because the reference checker currently only
accepts `cakeml/...sml` source paths. -/

namespace Flapjack.Test.FupdateListAppendCommutesParity

open Flapjack

private def lhsKeys : List (Nat × Nat) := [(1, 10), (2, 20)]
private def rhsKeys : List (Nat × Nat) := [(3, 30)]
private def overlappingKeys : List (Nat × Nat) := [(1, 99)]
private def baseMap : FiniteMap Nat Nat := FUPDATE_HOL FEMPTY (4, 40)

private theorem disjointKeys :
    ∀ key, key ∈ lhsKeys.map Prod.fst → key ∉ rhsKeys.map Prod.fst := by
  intro key hkey
  simp [lhsKeys, rhsKeys] at hkey ⊢
  rcases hkey with rfl | rfl <;> decide

/-- Kernel-checked use of the theorem for two key-disjoint update lists. -/
theorem disjointAppendCommutes :
    FUPDATE_LIST_HOL (FUPDATE_LIST_HOL baseMap lhsKeys) rhsKeys =
      FUPDATE_LIST_HOL (FUPDATE_LIST_HOL baseMap rhsKeys) lhsKeys :=
  FUPDATE_LIST_APPEND_COMMUTES_HOL lhsKeys rhsKeys baseMap disjointKeys

/-- The premise excludes shared keys; for an overlap the update order matters. -/
theorem overlapPremiseFails :
    ¬ ∀ key, key ∈ lhsKeys.map Prod.fst → key ∉ overlappingKeys.map Prod.fst := by
  intro h
  have hKey := h 1 (by simp [lhsKeys])
  simp [overlappingKeys] at hKey

theorem overlapLeftLookup :
    FLOOKUP (FUPDATE_LIST_HOL (FUPDATE_LIST_HOL baseMap lhsKeys) overlappingKeys) 1 = some 99 := by
  rfl

theorem overlapRightLookup :
    FLOOKUP (FUPDATE_LIST_HOL (FUPDATE_LIST_HOL baseMap overlappingKeys) lhsKeys) 1 = some 10 := by
  rfl

private def disjointLookupGuard : Bool :=
  (FLOOKUP (FUPDATE_LIST_HOL (FUPDATE_LIST_HOL baseMap lhsKeys) rhsKeys) 1 == some 10) &&
  (FLOOKUP (FUPDATE_LIST_HOL (FUPDATE_LIST_HOL baseMap lhsKeys) rhsKeys) 3 == some 30) &&
  (FLOOKUP (FUPDATE_LIST_HOL (FUPDATE_LIST_HOL baseMap lhsKeys) rhsKeys) 4 == some 40) &&
  (FLOOKUP (FUPDATE_LIST_HOL (FUPDATE_LIST_HOL baseMap lhsKeys) rhsKeys) 1 ==
    FLOOKUP (FUPDATE_LIST_HOL (FUPDATE_LIST_HOL baseMap rhsKeys) lhsKeys) 1)

private def overlapLookupGuard : Bool :=
  (FLOOKUP (FUPDATE_LIST_HOL (FUPDATE_LIST_HOL baseMap lhsKeys) overlappingKeys) 1 == some 99) &&
  (FLOOKUP (FUPDATE_LIST_HOL (FUPDATE_LIST_HOL baseMap overlappingKeys) lhsKeys) 1 == some 10) &&
  (FLOOKUP (FUPDATE_LIST_HOL (FUPDATE_LIST_HOL baseMap lhsKeys) overlappingKeys) 1 !=
    FLOOKUP (FUPDATE_LIST_HOL (FUPDATE_LIST_HOL baseMap overlappingKeys) lhsKeys) 1)

#guard disjointLookupGuard
#guard overlapLookupGuard

def runChecks : IO Bool := do
  let ok := disjointLookupGuard && overlapLookupGuard
  IO.println (if ok then
    "PASS FUPDATE_LIST_APPEND_COMMUTES disjoint/overlap cases match HOL"
    else "FAIL FUPDATE_LIST_APPEND_COMMUTES disjoint/overlap cases match HOL")
  return ok

end Flapjack.Test.FupdateListAppendCommutesParity
