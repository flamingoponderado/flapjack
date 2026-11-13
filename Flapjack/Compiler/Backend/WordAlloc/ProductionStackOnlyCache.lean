module

public import Flapjack.Compiler.Backend.WordAlloc.ProductionStackOnlySets
public import Flapjack.RiscV.CakeRegAlloc

@[expose] public section

namespace Flapjack.WordAlloc
open RiscV RiscV.CakeRegAlloc

/-! Invariants for the actual TreeSet accelerator used by cakeGetStackOnly.
These are untagged implementation proofs with no independent HOL original.
The caches observe the list membership, and distinctness discharges the
first-occurrence deletion issue. Neither invariant assumes the final native
analysis result. -/

def StackCacheRep (names : List Nat) (seen : Std.TreeSet Nat) : Prop :=
  ∀ key, key ∈ seen ↔ key ∈ names

def StackCacheValid (names : List Nat) (seen : Std.TreeSet Nat) : Prop :=
  names.Nodup ∧ StackCacheRep names seen

theorem stackCache_contains {names : List Nat} {seen : Std.TreeSet Nat}
    (rep : StackCacheRep names seen) (key : Nat) :
    seen.contains key = decide (key ∈ names) := by
  by_cases member : key ∈ names
  · simpa [member] using (Std.TreeSet.contains_iff_mem).mpr ((rep key).mpr member)
  · simpa [member] using Bool.eq_false_iff.mpr (fun h => member ((rep key).mp (Std.TreeSet.contains_iff_mem.mp h)))

private theorem unitMembers (names : List Nat) (key : Nat) :
    key ∈ natSetOfList names ↔ key ∈ names := by
  have same := RegAlloc.stackOnlyCodec_production names key
  rw [stackNamesTree_lookup] at same
  by_cases member : key ∈ names
  · simp only [member, ite_true, Option.isSome_some] at same
    exact ⟨fun _ => member, fun _ => Std.TreeSet.contains_iff_mem.mp same⟩
  · simp only [member, ite_false, Option.isSome_none] at same
    exact ⟨fun h => by have yes := Std.TreeSet.contains_iff_mem.mpr h; rw [same] at yes; contradiction,
      fun h => False.elim (member h)⟩

theorem stackCache_initial (names : List Nat) (unique : names.Nodup) :
    StackCacheValid names (natSetOfList names) := ⟨unique, unitMembers names⟩

private theorem insertFold_members (keys : List Nat) (seen : Std.TreeSet Nat) (key : Nat) :
    key ∈ keys.foldl (fun seen name => seen.insert name) seen ↔ key ∈ keys ∨ key ∈ seen := by
  induction keys generalizing seen with
  | nil => simp
  | cons name keys ih =>
      simp only [List.foldl_cons, ih, Std.TreeSet.mem_insert,
        Std.LawfulEqCmp.compare_eq_iff_eq, List.mem_cons]
      simp only [or_assoc, or_left_comm, eq_comm]

private theorem eraseFold_members (keys : List Nat) (seen : Std.TreeSet Nat) (key : Nat) :
    key ∈ keys.foldl (fun seen name => seen.erase name) seen ↔ key ∈ seen ∧ key ∉ keys := by
  induction keys generalizing seen with
  | nil => simp
  | cons name keys ih =>
      simp only [List.foldl_cons, ih, Std.TreeSet.mem_erase, ne_eq,
        Std.LawfulEqCmp.compare_eq_iff_eq, List.mem_cons]
      simp only [not_or, eq_comm, and_assoc, and_left_comm]

theorem stackCache_union (left right : List Nat) (seen : Std.TreeSet Nat)
    (valid : StackCacheValid left seen) (unique : right.Nodup) :
    let result := cakeStackOnlyUnion left seen right
    result.1 = CakeAlloc.unionSet left right ∧ StackCacheValid result.1 result.2 := by
  have same : ∀ key, seen.contains key = (natSetOfList left).contains key := by
    intro key
    rw [stackCache_contains valid.2, stackCache_contains (unitMembers left)]
  have projection : (cakeStackOnlyUnion left seen right).1 = CakeAlloc.unionSet left right := by
    simp only [cakeStackOnlyUnion, CakeAlloc.unionSet, same]
  refine ⟨projection, ⟨projection ▸ stackUnion_nodup _ _ valid.1 unique, ?_⟩⟩
  intro key
  simp only [cakeStackOnlyUnion, insertFold_members, valid.2 key,
    List.mem_append, List.mem_filter, stackCache_contains valid.2]
  by_cases l : key ∈ left <;> by_cases r : key ∈ right <;> simp [l, r]

theorem stackCache_diff (left right : List Nat) (leftSeen rightSeen : Std.TreeSet Nat)
    (valid : StackCacheValid left leftSeen) (rep : StackCacheRep right rightSeen) :
    let result := cakeStackOnlyDiff left leftSeen rightSeen right
    result.1 = CakeAlloc.diffSet left right ∧ StackCacheValid result.1 result.2 := by
  have same : ∀ key, rightSeen.contains key = (natSetOfList right).contains key := by
    intro key
    rw [stackCache_contains rep, stackCache_contains (unitMembers right)]
  refine ⟨?_, ⟨valid.1.filter _, ?_⟩⟩
  · simp only [cakeStackOnlyDiff, CakeAlloc.diffSet, same]
  · intro key
    simp only [cakeStackOnlyDiff, eraseFold_members, valid.2 key,
      List.mem_filter, stackCache_contains rep]
    simp

end Flapjack.WordAlloc
