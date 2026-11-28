module

public import Flapjack.Misc.Sptree
public import Flapjack.Misc.Sptree.FromList
public import Flapjack.Misc.Sptree.FromList2
public import Flapjack.Misc.Sptree.FromList.Domain
public import Mathlib.Algebra.Group.Nat.Even

@[expose] public section

/-!
# Lookup in the even-key sparse tree

Counterparts of `lookup_fromList2` and `fromList2_value` from
`cakeml/misc/miscScript.sml`: `fromList2` inserts the list elements at the even
keys `0, 2, 4, …`, so an even-key lookup agrees with the sequential
`fromList` lookup at half the key, and an element is present exactly when some
key maps to it.
-/

namespace Flapjack

/-- Flapjack infrastructure: the sequential fold appends one inserted key. -/
theorem sptFromListFoldIndex {α : Type} (values : List α) (start : Nat) (tree : Spt α) :
    (values.foldl (fun (acc : Nat × Spt α) value => (acc.1 + 1, sptInsert acc.1 value acc.2))
      (start, tree)).1 = start + values.length := by
  induction values generalizing start tree with
  | nil => simp
  | cons value values ih =>
    simp only [List.foldl_cons, ih, List.length_cons, Nat.add_assoc, Nat.add_comm 1]

/-- Flapjack infrastructure: the sequential fold appends one inserted key. -/
theorem sptFromList_append_singleton {α : Type} (values : List α) (value : α) :
    sptFromList (values ++ [value]) =
      sptInsert values.length value (sptFromList values) := by
  simp only [sptFromList, List.foldl_append, List.foldl_cons, List.foldl_nil,
    sptFromListFoldIndex, Nat.zero_add]

/-- Flapjack infrastructure: the even-key fold appends one inserted key. -/
theorem sptFromList2_append_singleton {α : Type} (values : List α) (value : α) :
    sptFromList2 (values ++ [value]) =
      sptInsert (2 * values.length) value (sptFromList2 values) := by
  simp only [sptFromList2, List.foldl_append, List.foldl_cons, List.foldl_nil,
    sptFromList2FoldIndex, Nat.zero_add]

/-- Original `lookup_fromList2`. -/
@[hol "cakeml/misc/miscScript.sml" "lookup_fromList2"]
theorem sptLookupFromList2 {α : Type} (values : List α) (key : Nat) :
    sptLookup key (sptFromList2 values) =
      if Even key then sptLookup (key / 2) (sptFromList values) else none := by
  induction values using List.reverseRecOn with
  | nil =>
    simp [sptFromList2, sptFromList]
  | append_singleton values value ih =>
    rw [sptFromList2_append_singleton, sptFromList_append_singleton]
    by_cases hparity : Even key
    · rw [if_pos hparity]
      by_cases hkey : key = 2 * values.length
      · have hhalfLen : 2 * values.length / 2 = values.length := by omega
        rw [hkey, hhalfLen, sptLookup_sptInsert_same, sptLookup_sptInsert_same]
      · obtain ⟨half, hhalf⟩ := hparity
        have hhalfNe : key / 2 ≠ values.length := by omega
        rw [sptLookup_sptInsert_ne (2 * values.length) key value (sptFromList2 values) hkey,
          ih, if_pos ⟨half, hhalf⟩]
        exact (sptLookup_sptInsert_ne values.length (key / 2) value (sptFromList values)
          hhalfNe).symm
    · rw [if_neg hparity]
      by_cases hkey : key = 2 * values.length
      · exfalso
        have heven : Even (2 * values.length) := ⟨values.length, by omega⟩
        rw [hkey] at hparity
        exact hparity heven
      · rw [sptLookup_sptInsert_ne (2 * values.length) key value (sptFromList2 values) hkey,
          ih, if_neg hparity]

/-- Original `fromList2_value`: the HOL statement carries the vacuous binders
`t` and `n`, which are omitted here (they occur nowhere in the body). -/
@[hol "cakeml/misc/miscScript.sml" "fromList2_value"]
theorem fromList2Value {α : Type} (element : α) (values : List α) :
    element ∈ values ↔ ∃ key, sptLookup key (sptFromList2 values) = some element := by
  constructor
  · intro hmem
    obtain ⟨index, hbound, hvalue⟩ := List.mem_iff_getElem.mp hmem
    refine ⟨2 * index, ?_⟩
    rw [sptLookupFromList2, if_pos ⟨index, by omega⟩]
    have hhalf : 2 * index / 2 = index := by omega
    rw [hhalf, sptLookupFromList, dif_pos hbound, hvalue]
  · intro ⟨key, hkey⟩
    by_cases hparity : Even key
    · rw [sptLookupFromList2, if_pos hparity] at hkey
      rw [sptLookupFromList] at hkey
      by_cases hbound : key / 2 < values.length
      · rw [dif_pos hbound] at hkey
        have hvalue : values[key / 2]'hbound = element := Option.some.inj hkey
        exact List.mem_iff_getElem.mpr ⟨key / 2, hbound, hvalue⟩
      · rw [dif_neg hbound] at hkey
        exact absurd hkey (by simp)
    · rw [sptLookupFromList2, if_neg hparity] at hkey
      exact absurd hkey (by simp)

end Flapjack
