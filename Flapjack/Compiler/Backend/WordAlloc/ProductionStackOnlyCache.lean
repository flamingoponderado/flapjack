import Flapjack.Compiler.Backend.WordAlloc.ProductionStackOnlySets
import Flapjack.RiscV.CakeRegAlloc

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
  · simp only [member, if_true, Option.isSome_some] at same
    exact ⟨fun _ => member, fun _ => Std.TreeSet.contains_iff_mem.mp same⟩
  · simp only [member, if_false, Option.isSome_none] at same
    exact ⟨fun h => by have yes := Std.TreeSet.contains_iff_mem.mpr h; rw [same] at yes; contradiction,
      fun h => False.elim (member h)⟩

theorem stackCache_initial (names : List Nat) (unique : names.Nodup) :
    StackCacheValid names (natSetOfList names) := ⟨unique, unitMembers names⟩

theorem stackCache_insert (key : Nat) (names : List Nat) (seen : Std.TreeSet Nat)
    (valid : StackCacheValid names seen) :
    let result := cakeStackOnlyInsert key names seen
    result.1 = CakeAlloc.insertSet key names ∧ StackCacheValid result.1 result.2 := by
  have contains := stackCache_contains valid.2 key
  unfold cakeStackOnlyInsert CakeAlloc.insertSet
  by_cases member : key ∈ names
  · simp [contains, member, valid]
  · simp only [contains, decide_false, Bool.false_eq_true, if_false,
      List.contains_iff_mem, member]
    refine ⟨True.intro, ⟨List.nodup_cons.mpr ⟨member, valid.1⟩, ?_⟩⟩
    intro other
    simp only [Std.TreeSet.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
      valid.2 other, List.mem_cons]
    simp only [eq_comm]

theorem stackCache_delete (key : Nat) (names : List Nat) (seen : Std.TreeSet Nat)
    (valid : StackCacheValid names seen) :
    let result := cakeStackOnlyDelete key names seen
    result.1 = CakeAlloc.deleteSet key names ∧ StackCacheValid result.1 result.2 := by
  refine ⟨rfl, ⟨valid.1.erase key, ?_⟩⟩
  intro other
  simp only [cakeStackOnlyDelete, Std.TreeSet.mem_erase,
    ne_eq, Std.LawfulEqCmp.compare_eq_iff_eq, valid.2 other, valid.1.mem_erase_iff]
  simp only [eq_comm]

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

theorem stackCache_inter (left right : List Nat) (seen : Std.TreeSet Nat)
    (unique : left.Nodup) (rep : StackCacheRep right seen) :
    let result := cakeStackOnlyInter left seen
    result.1 = CakeAlloc.interSet left right ∧ StackCacheValid result.1 result.2 := by
  have same : ∀ key, seen.contains key = (natSetOfList right).contains key := by
    intro key
    rw [stackCache_contains rep, stackCache_contains (unitMembers right)]
  refine ⟨?_, stackCache_initial _ (unique.filter _)⟩
  simp only [cakeStackOnlyInter, CakeAlloc.interSet, same]

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


def StackStateValid (state : CakeStackOnlyState) : Prop :=
  StackCacheValid state.ts state.tsSet ∧ StackCacheValid state.fs state.fsSet

abbrev stackStatePair (state : CakeStackOnlyState) : List Nat × List Nat :=
  (state.ts, state.fs)

theorem stackState_initial (pair : List Nat × List Nat)
    (unique : pair.1.Nodup ∧ pair.2.Nodup) :
    StackStateValid (cakeStackOnlyStateOfPair pair) :=
  ⟨stackCache_initial _ unique.1, stackCache_initial _ unique.2⟩

theorem stackCache_move (x y : Nat) (state : CakeStackOnlyState)
    (valid : StackStateValid state) :
    stackStatePair (cakeStackOnlyMergeMove x y state) =
      CakeAlloc.mergeStackOnly x y state.ts state.fs ∧
      StackStateValid (cakeStackOnlyMergeMove x y state) := by
  have tsInsert := stackCache_insert y state.ts state.tsSet valid.1
  have fsInsert := stackCache_insert x state.fs state.fsSet valid.2
  have tsDelete := stackCache_delete y state.ts state.tsSet valid.1
  have tsValid := tsInsert.2
  rw [tsInsert.1] at tsValid
  have fsValid := fsInsert.2
  rw [fsInsert.1] at fsValid
  have delValid := tsDelete.2
  rw [tsDelete.1] at delValid
  have contains := stackCache_contains valid.1.2 x
  by_cases alloc : CakeAlloc.isAllocVar y = true <;>
    by_cases physical : CakeAlloc.isPhyVar y = true <;>
    by_cases stack : CakeAlloc.isStackVar x = true <;>
    by_cases member : x ∈ state.ts <;>
    simp_all [cakeStackOnlyMergeMove, CakeAlloc.mergeStackOnly, stackStatePair,
      StackStateValid]

theorem stackCache_remove (keys : List Nat) (state : CakeStackOnlyState)
    (valid : StackStateValid state) :
    stackStatePair (cakeStackOnlyDeleteMany keys state) =
      CakeAlloc.removeTempStack keys state.ts state.fs ∧
      StackStateValid (cakeStackOnlyDeleteMany keys state) := by
  induction keys with
  | nil => exact ⟨rfl, valid⟩
  | cons key keys ih =>
      let rest := cakeStackOnlyDeleteMany keys state
      have deletion := stackCache_delete key rest.ts rest.tsSet ih.2.1
      have same : rest.ts = keys.foldr CakeAlloc.deleteSet state.ts :=
        congrArg Prod.fst ih.1
      have fixed : rest.fs = state.fs := congrArg Prod.snd ih.1
      refine ⟨?_, ⟨deletion.2, ih.2.2⟩⟩
      change ((cakeStackOnlyDelete key rest.ts rest.tsSet).1, rest.fs) =
        (CakeAlloc.deleteSet key (keys.foldr CakeAlloc.deleteSet state.ts), state.fs)
      rw [deletion.1, same, fixed]


theorem stackCache_merge (base left right : CakeStackOnlyState)
    (hb : StackStateValid base) (hl : StackStateValid left) (hr : StackStateValid right) :
    stackStatePair (cakeStackOnlyMergeSets base left right) =
      CakeAlloc.mergeStackSets base.ts base.fs left.ts left.fs right.ts right.fs ∧
      StackStateValid (cakeStackOnlyMergeSets base left right) := by
  let inner := cakeStackOnlyInter left.ts base.tsSet
  have hi := stackCache_inter left.ts base.ts base.tsSet hl.1.1 hb.1.2
  let common := cakeStackOnlyInter right.ts inner.2
  have hc := stackCache_inter right.ts inner.1 inner.2 hr.1.1 hi.2.2
  let leftOnly := left.ts.filter (fun key => !base.tsSet.contains key)
  let rightOnly := right.ts.filter (fun key => !base.tsSet.contains key)
  have leftEq : leftOnly = CakeAlloc.diffSet left.ts base.ts := by
    have same : ∀ key, base.tsSet.contains key = (natSetOfList base.ts).contains key := by
      intro key
      rw [stackCache_contains hb.1.2, stackCache_contains (unitMembers base.ts)]
    simp only [leftOnly, CakeAlloc.diffSet, same]
  have rightEq : rightOnly = CakeAlloc.diffSet right.ts base.ts := by
    have same : ∀ key, base.tsSet.contains key = (natSetOfList base.ts).contains key := by
      intro key
      rw [stackCache_contains hb.1.2, stackCache_contains (unitMembers base.ts)]
    simp only [rightOnly, CakeAlloc.diffSet, same]
  let different := cakeStackOnlyUnion leftOnly (natSetOfList leftOnly) rightOnly
  have hd := stackCache_union leftOnly rightOnly (natSetOfList leftOnly)
    (stackCache_initial _ (hl.1.1.filter _)) (hr.1.1.filter _)
  let temporary := cakeStackOnlyUnion common.1 common.2 different.1
  have ht := stackCache_union common.1 different.1 common.2 hc.2 hd.2.1
  let fixed := cakeStackOnlyUnion left.fs left.fsSet right.fs
  have hf := stackCache_union left.fs right.fs left.fsSet hl.2 hr.2.1
  have eqState : cakeStackOnlyMergeSets base left right =
      { ts := temporary.1, tsSet := temporary.2, fs := fixed.1, fsSet := fixed.2 } := rfl
  rw [eqState]
  refine ⟨?_, ⟨ht.2, hf.2⟩⟩
  change (temporary.1, fixed.1) = _
  rw [ht.1, hf.1, hc.1, hd.1, hi.1, leftEq, rightEq]
  rfl

end Flapjack.WordAlloc


