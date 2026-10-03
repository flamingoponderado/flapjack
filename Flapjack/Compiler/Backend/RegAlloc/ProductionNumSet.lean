import Flapjack.Compiler.Backend.RegAlloc.ProductionInitTags
import Flapjack.NumSet

namespace Flapjack.RegAlloc

/-- Constructor codec for the actual unit tree used at allocator input
boundaries. Flapjack infrastructure, not a HOL datatype declaration. -/
def productionNumSetToNative : Flapjack.NumSet.Tree → NumSet
  | .empty => .ln
  | .singleton => .ls ()
  | .branch left right => .bn (productionNumSetToNative left) (productionNumSetToNative right)
  | .branchSingleton left right => .bs (productionNumSetToNative left) () (productionNumSetToNative right)

/-- The actual insertion fuel suffices from its numeric key; no supplied
insertion result is assumed. Untagged actual/native carrier correspondence. -/
theorem numSetInsertFuel_production (fuel key : Nat) (tree : Flapjack.NumSet.Tree)
    (sufficient : key < fuel) :
    productionNumSetToNative (Flapjack.NumSet.insertFuel fuel key tree) =
      sptInsert key () (productionNumSetToNative tree) := by
  induction fuel generalizing key tree with
  | zero => omega
  | succ fuel ih =>
    cases key with
    | zero => cases tree <;> simp [Flapjack.NumSet.insertFuel, productionNumSetToNative, sptInsert]
    | succ key =>
      have child : key / 2 < fuel := by omega
      cases tree <;> by_cases parity : (key + 1) % 2 = 0
      all_goals simp only [Flapjack.NumSet.insertFuel, parity, ↓reduceIte, productionNumSetToNative]
      all_goals rw [sptInsert]
      all_goals simp only [Nat.succ_ne_zero, ↓reduceIte, parity, Nat.succ_sub_one, ih _ _ child]
      all_goals rfl

/-- The executed wrapper discharges insertion fuel unconditionally. -/
theorem numSetInsert_production (key : Nat) (tree : Flapjack.NumSet.Tree) :
    productionNumSetToNative (Flapjack.NumSet.insert key tree) =
      sptInsert key () (productionNumSetToNative tree) :=
  numSetInsertFuel_production (key + 1) key tree (by omega)

private theorem lrnextFuel_production (fuel key : Nat) (sufficient : key < fuel) :
    Flapjack.NumSet.lrnextFuel fuel key = lrNext key := by
  induction fuel generalizing key with
  | zero => omega
  | succ fuel ih =>
    cases key with
    | zero => simp only [Flapjack.NumSet.lrnextFuel, lrNext]
    | succ key =>
      have child : key / 2 < fuel := by omega
      simp only [Flapjack.NumSet.lrnextFuel, lrNext, ih _ child]

/-- Actual traversal increments match native lrNext, with wrapper fuel derived
from its input. Untagged external-library correspondence infrastructure. -/
theorem numSetLrnext_production (key : Nat) : Flapjack.NumSet.lrnext key = lrNext key :=
  lrnextFuel_production (key + 1) key (by omega)

/-- Full mixed traversal order, including the accumulator, matches native
sptFoldi. Neither ascending order nor an output-order equality is assumed.
This is actual/native infrastructure without a separate HOL original. -/
theorem numSetToAList_production (tree : Flapjack.NumSet.Tree) (index : Nat) (accumulator : List Nat) :
    sptFoldi (fun key value accumulated => (key, value) :: accumulated) index
      (accumulator.map (fun key => (key, ()))) (productionNumSetToNative tree) =
      (Flapjack.NumSet.toAList tree index accumulator).map (fun key => (key, ())) := by
  induction tree generalizing index accumulator with
  | empty => rfl
  | singleton => rfl
  | branch left right leftIH rightIH =>
    simp only [productionNumSetToNative, sptFoldi, Flapjack.NumSet.toAList,
      numSetLrnext_production, leftIH, rightIH]
  | branchSingleton left right leftIH rightIH =>
    simp only [productionNumSetToNative, sptFoldi, Flapjack.NumSet.toAList,
      numSetLrnext_production, leftIH]
    simpa only [List.map_cons] using rightIH (index + lrNext index)
      (index :: Flapjack.NumSet.toAList left (index + 2 * lrNext index) accumulator)

private theorem insertionFold_production (names : List Nat) (tree : Flapjack.NumSet.Tree) :
    productionNumSetToNative (names.foldl (fun tree key => Flapjack.NumSet.insert key tree) tree) =
      names.foldl (fun tree key => sptInsert key () tree) (productionNumSetToNative tree) := by
  induction names generalizing tree with
  | nil => rfl
  | cons name rest ih => simp only [List.foldl_cons, ih, numSetInsert_production]

private theorem unitInsert_commute (first second : Nat) (tree : NumSet) :
    sptInsert first () (sptInsert second () tree) = sptInsert second () (sptInsert first () tree) := by
  by_cases equal : first = second
  · subst second; rfl
  · exact sptInsert_swap first second () () tree equal

private theorem insertionFold_push (names : List Nat) (tree : NumSet) (key : Nat) :
    names.foldl (fun tree key => sptInsert key () tree) (sptInsert key () tree) =
      sptInsert key () (names.foldl (fun tree key => sptInsert key () tree) tree) := by
  induction names generalizing tree with
  | nil => rfl
  | cons name rest ih =>
    rw [List.foldl_cons, unitInsert_commute name key tree, ih, List.foldl_cons]

private theorem insertionFold_fromAList (names : List Nat) :
    names.foldl (fun tree key => sptInsert key () tree) .ln =
      sptFromAList (names.map (fun key => (key, ()))) := by
  induction names with
  | nil => rfl
  | cons name rest ih => rw [List.foldl_cons, insertionFold_push, ih]; rfl

/-- Full actual reconstruction/enumeration agrees with original fromAList and
toAList on canonical unit associations, for arbitrary input key lists including
duplicates. This is untagged production carrier correspondence. -/
theorem numSetFromAList_production (names : List Nat) :
    (Flapjack.NumSet.fromAList names).map (fun key => (key, ())) =
      sptToAList (sptFromAList (names.map (fun key => (key, ())))) := by
  unfold Flapjack.NumSet.fromAList sptToAList
  have insertion := insertionFold_production names .empty
  simp only [productionNumSetToNative] at insertion
  rw [← insertionFold_fromAList, ← insertion]
  exact (numSetToAList_production _ 0 []).symm

private theorem unitAssociations (entries : List (Nat × Unit)) :
    (entries.map Prod.fst).map (fun key => (key, ())) = entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, payload⟩ := entry
    cases payload
    simp only [List.map_cons, ih]

/-- The actual Set/Branch input boundary preserves precisely the original
well-formed tree's mixed key order after its reconstruction step. This
discharges the real enumeration premise needed by allocator node numbering;
no sorted-order or desired output-order premise is introduced. -/
theorem numSetFromAList_nativeKeys (tree : NumSet) (wellFormed : sptWf tree = true) :
    Flapjack.NumSet.fromAList ((sptToAList tree).map Prod.fst) =
      (sptToAList tree).map Prod.fst := by
  have codec := numSetFromAList_production ((sptToAList tree).map Prod.fst)
  rw [unitAssociations] at codec
  have reconstructed : sptFromAList (sptToAList tree) = tree :=
    (sptEqThm _ _ ⟨sptWfFromAList _, wellFormed⟩).mpr
      (fun key => sptLookup_sptFromAList_sptToAList key tree)
  rw [reconstructed] at codec
  have keys := congrArg (List.map Prod.fst) codec
  simpa [List.map_map, Function.comp_def] using keys

end Flapjack.RegAlloc
