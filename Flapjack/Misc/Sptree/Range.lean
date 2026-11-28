module

public import Flapjack.Misc.Sptree
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Lattice

@[expose] public section

/-!
# HOL `sptree` range, shape equality and misc `range` lemmas

Counterparts of `cakeml/misc/miscScript.sml`'s `range_def`, `range_insert`,
`range_insert_SUBSET` and `eq_shape_def` over the tagged `Spt` carrier. The
`Set` imports live in this module rather than in `Flapjack.Misc.Sptree`, whose
importers are numerous and sensitive to the simp set.
-/

namespace Flapjack

/-- Exact HOL `range_def`: the set of values stored in a sparse tree. -/
@[hol "cakeml/misc/miscScript.sml" "range_def"]
def sptRange {α : Type} (tree : Spt α) : Set α := {v | ∃ n, sptLookup n tree = some v}

/-- Original `range_insert_SUBSET`: inserting a value keeps the range inside the
old range plus the new value. -/
@[hol "cakeml/misc/miscScript.sml" "range_insert_SUBSET"]
theorem rangeInsertSubset {α : Type} (n : Nat) (l : α) (fml : Spt α) :
    sptRange (sptInsert n l fml) ⊆ insert l (sptRange fml) := by
  intro w hw
  obtain ⟨m, hm⟩ := hw
  by_cases h : m = n
  · subst h
    rw [sptLookup_sptInsert_same] at hm
    rw [Set.mem_insert_iff]
    exact Or.inl (Option.some.inj hm.symm)
  · rw [sptLookup_sptInsert_ne n m l fml h] at hm
    exact Set.mem_insert_of_mem l ⟨m, hm⟩

/-- Original `range_insert`: inserting a value at an absent key adds exactly
that value to the range. -/
@[hol "cakeml/misc/miscScript.sml" "range_insert"]
theorem rangeInsert {α : Type} (n : Nat) (l : α) (fml : Spt α)
    (h : ¬ sptDomain fml n) : sptRange (sptInsert n l fml) = insert l (sptRange fml) := by
  apply Set.Subset.antisymm
  · exact rangeInsertSubset n l fml
  · intro w hw
    rw [Set.mem_insert_iff] at hw
    rcases hw with heq | hw
    · rw [heq]
      exact ⟨n, sptLookup_sptInsert_same n l fml⟩
    · obtain ⟨m, hm⟩ := hw
      have hne : m ≠ n := by
        intro heq
        apply h
        rw [← heq]
        exact (sptDomain_iff_lookup fml m).mpr ⟨w, hm⟩
      refine ⟨m, ?_⟩
      rw [sptLookup_sptInsert_ne n m l fml hne]
      exact hm

/-- Exact HOL `eq_shape_def`: the two trees have the same shape, comparing only
the branch structure and ignoring stored values. -/
@[hol "cakeml/misc/miscScript.sml" "eq_shape_def"]
def sptEqShape {α β : Type} : Spt α → Spt β → Bool
  | .ln, .ln => true
  | .ls _, .ls _ => true
  | .bn l1 l2, .bn r1 r2 => sptEqShape l1 r1 && sptEqShape l2 r2
  | .bs l1 _ l2, .bs r1 _ r2 => sptEqShape l1 r1 && sptEqShape l2 r2
  | _, _ => false

end Flapjack
