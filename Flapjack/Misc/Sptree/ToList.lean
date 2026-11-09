module

public import Flapjack.Misc.Sptree
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Traversal of the literal sparse-tree representation. -/
namespace Flapjack

/-- Collect tree values into an accumulator in the original traversal order. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "toListA_def"]
def sptToListA {α : Type} (acc : List α) : Spt α → List α
  | .ln => acc
  | .ls value => value :: acc
  | .bn left right => sptToListA (sptToListA acc right) left
  | .bs left value right => sptToListA (value :: sptToListA acc right) left

/-- Collect all values from a sparse tree. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "toList_def"]
def sptToList {α : Type} (tree : Spt α) : List α := sptToListA [] tree

/-- Existence of a lookup in a branch is the disjunction of its children.
This is proof infrastructure for the original sparse-tree membership lemma. -/
private theorem lookup_bn_exists {α : Type} (left right : Spt α) (value : α) :
    (∃ key, sptLookup key (.bn left right) = some value) ↔
      (∃ key, sptLookup key left = some value) ∨ (∃ key, sptLookup key right = some value) := by
  constructor
  · rintro ⟨key, found⟩
    by_cases zero : key = 0
    · simp [sptLookup, zero] at found
    · by_cases even : key % 2 = 0
      · left; exact ⟨(key - 1) / 2, by simpa [sptLookup, zero, even] using found⟩
      · right; exact ⟨(key - 1) / 2, by simpa [sptLookup, zero, even] using found⟩
  · rintro (⟨key, found⟩ | ⟨key, found⟩)
    · refine ⟨2 * key + 2, ?_⟩
      have nonzero : 2 * key + 2 ≠ 0 := by omega
      have even : (2 * key + 2) % 2 = 0 := by omega
      have half : (2 * key + 1) / 2 = key := by omega
      simpa [sptLookup, nonzero, even, half] using found
    · refine ⟨2 * key + 1, ?_⟩
      have nonzero : 2 * key + 1 ≠ 0 := by omega
      have odd : (2 * key + 1) % 2 ≠ 0 := by omega
      have half : (2 * key + 1 - 1) / 2 = key := by omega
      simpa [sptLookup, nonzero, odd, half] using found

/-- Existence of a lookup in a value-bearing branch includes the root value. -/
private theorem lookup_bs_exists {α : Type} (left right : Spt α) (root value : α) :
    (∃ key, sptLookup key (.bs left root right) = some value) ↔
      root = value ∨ (∃ key, sptLookup key left = some value) ∨ (∃ key, sptLookup key right = some value) := by
  constructor
  · rintro ⟨key, found⟩
    by_cases zero : key = 0
    · left; simpa [sptLookup, zero] using found
    · by_cases even : key % 2 = 0
      · exact .inr (.inl ⟨(key - 1) / 2, by simpa [sptLookup, zero, even] using found⟩)
      · exact .inr (.inr ⟨(key - 1) / 2, by simpa [sptLookup, zero, even] using found⟩)
  · rintro (equal | ⟨key, found⟩ | ⟨key, found⟩)
    · exact ⟨0, by simpa [sptLookup] using equal⟩
    · refine ⟨2 * key + 2, ?_⟩
      have nonzero : 2 * key + 2 ≠ 0 := by omega
      have even : (2 * key + 2) % 2 = 0 := by omega
      have half : (2 * key + 1) / 2 = key := by omega
      simpa [sptLookup, nonzero, even, half] using found
    · refine ⟨2 * key + 1, ?_⟩
      have nonzero : 2 * key + 1 ≠ 0 := by omega
      have odd : (2 * key + 1) % 2 ≠ 0 := by omega
      have half : (2 * key + 1 - 1) / 2 = key := by omega
      simpa [sptLookup, nonzero, odd, half] using found

/-- Membership in the accumulator traversal is exactly membership in the
accumulator or the range of the tree lookup. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "MEM_toListA"]
theorem sptMemToListA {α : Type} (tree : Spt α) (acc : List α) (value : α) :
    value ∈ sptToListA acc tree ↔ value ∈ acc ∨ ∃ key, sptLookup key tree = some value := by
  induction tree generalizing acc with
  | ln => simp [sptToListA, sptLookup]
  | ls root =>
    simp only [sptToListA, List.mem_cons]
    constructor
    · rintro (equal | member)
      · right; exact ⟨0, by simpa [sptLookup] using equal.symm⟩
      · exact .inl member
    · rintro (member | ⟨key, found⟩)
      · exact .inr member
      · by_cases zero : key = 0
        · left; simpa [sptLookup, zero] using found.symm
        · simp [sptLookup, zero] at found
  | bn left right ihLeft ihRight =>
    simp only [sptToListA, ihLeft, ihRight, lookup_bn_exists]
    simp [or_left_comm, or_comm]
  | bs left root right ihLeft ihRight =>
    simp only [sptToListA, ihLeft, ihRight, List.mem_cons, lookup_bs_exists]
    simp [or_left_comm, or_comm, eq_comm]

/-- The values in a sparse tree are precisely the values returned by lookup. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "MEM_toList"]
theorem sptMemToList {α : Type} (value : α) (tree : Spt α) :
    value ∈ sptToList tree ↔ ∃ key, sptLookup key tree = some value := by
  simp [sptToList, sptMemToListA]

end Flapjack
