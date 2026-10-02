import Flapjack.Compiler.Backend.RegAlloc.ProductionInputCodec

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc

private theorem insertOrdered (node : Nat) (row : List Nat)
    (ordered : row.Pairwise (· > ·)) : (cakeSortedInsert node row).Pairwise (· > ·) := by
  induction row with
  | nil => simp [cakeSortedInsert_nil]
  | cons head rest ih =>
    obtain ⟨headGreater, restOrdered⟩ := List.pairwise_cons.mp ordered
    rw [cakeSortedInsert_cons]
    by_cases equal : node = head
    · simp only [equal, ↓reduceIte]; exact List.pairwise_cons.mpr ⟨headGreater, restOrdered⟩
    · simp only [equal, ↓reduceIte]
      by_cases greater : node > head
      · simp only [greater, ↓reduceIte]
        refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨headGreater, restOrdered⟩⟩
        intro member present
        rcases List.mem_cons.mp present with rfl | present
        · exact greater
        · have bound := headGreater member present; omega
      · simp only [greater, ↓reduceIte]
        refine List.pairwise_cons.mpr ⟨?_, ih restOrdered⟩
        intro member present
        rcases (cakeSortedInsert_membership node member rest).mp present with rfl | present
        · omega
        · exact headGreater member present

private theorem setRowOrdered (set : Std.TreeSet Nat) :
    (cakeAdjSetList set).Pairwise (· > ·) := by
  have ordered := Std.TreeSet.ordered_toList (t := set)
  simpa [cakeAdjSetList, List.pairwise_reverse, Std.compare_eq_lt] using ordered

/-- Exact ordered materialization of one actual set insertion. Membership
alone would not establish the native adjacency iteration order. This is
untagged actual/native infrastructure, not a separate HOL declaration. -/
theorem cakeAdjSetList_insert (set : Std.TreeSet Nat) (node : Nat) :
    cakeAdjSetList (set.insert node) = cakeSortedInsert node (cakeAdjSetList set) := by
  have leftOrdered := setRowOrdered (set.insert node)
  have rightOrdered := insertOrdered node _ (setRowOrdered set)
  have leftUnique : (cakeAdjSetList (set.insert node)).Nodup :=
    leftOrdered.imp (fun {_ _} greater => by omega)
  have rightUnique : (cakeSortedInsert node (cakeAdjSetList set)).Nodup :=
    rightOrdered.imp (fun {_ _} greater => by omega)
  apply List.Perm.eq_of_pairwise (le := (· > ·))
    (fun _ _ _ _ first second => by omega) leftOrdered rightOrdered
  apply (List.perm_ext_iff_of_nodup leftUnique rightUnique).mpr
  intro member
  have membership := cakeAdjSetList_membership (set.insert node) member
  have oldMembership := cakeAdjSetList_membership set member
  simp only [Std.TreeSet.contains_insert, Bool.beq_eq_decide_eq,
    Std.LawfulEqCmp.compare_eq_iff_eq, ← oldMembership, ← Bool.decide_or] at membership
  simpa only [eq_comm] using
    (decide_eq_decide.mp membership).trans
      (by simpa only [eq_comm] using (cakeSortedInsert_membership node member (cakeAdjSetList set)).symm)

/-- Full map materialization commutes with executed edge insertion at every
key, including missing keys and equal endpoints. Both original endpoint rows
are read before either write. Untagged graph-producer correspondence. -/
theorem cakeInsertEdgeSet_materialize (cache : CakeNodeMap (Std.TreeSet Nat)) (x y key : Nat) :
    ((cakeInsertEdgeSet x y cache).mapValues cakeAdjSetList).get key =
      (cakeInsertEdge x y (cache.mapValues cakeAdjSetList)).get key := by
  rw [CakeNodeMap.get_mapValues]
  unfold cakeInsertEdgeSet cakeInsertEdge cakeAdjSub
  by_cases atY : key = y
  · subst key
    simp only [CakeNodeMap.get_set_self, Option.map_some,
      cakeAdjSetList_insert, CakeNodeMap.get_mapValues]
    cases cache.get y <;> rfl
  · rw [CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm atY),
      CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm atY)]
    by_cases atX : key = x
    · subst key
      simp only [CakeNodeMap.get_set_self, Option.map_some,
        cakeAdjSetList_insert, CakeNodeMap.get_mapValues]
      cases cache.get x <;> rfl
    · rw [CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm atX),
        CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm atX), CakeNodeMap.get_mapValues]

end Flapjack.RegAlloc
