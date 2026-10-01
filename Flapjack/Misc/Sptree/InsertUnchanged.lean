import Flapjack.Misc.Sptree

namespace Flapjack

/-- A present binding is unchanged by reinsertion of the same value.
The HOL statement has no well-formedness premise. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "insert_unchanged"]
theorem sptInsertUnchanged {α : Type} (tree : Spt α) (key : Nat) (value : α)
    (h : sptLookup key tree = some value) :
    sptInsert key value tree = tree := by
  induction tree generalizing key with
  | ln => simp [sptLookup] at h
  | ls old =>
      by_cases hz : key = 0
      · subst key
        simp [sptLookup] at h
        subst old
        rw [sptInsert]
        simp
      · simp [sptLookup, hz] at h
  | bn left right ihl ihr =>
      by_cases hz : key = 0
      · simp [sptLookup, hz] at h
      · by_cases he : key % 2 = 0
        · simp only [sptLookup, if_neg hz, if_pos he] at h
          rw [sptInsert]
          simp only [if_neg hz, if_pos he, ihl _ h]
        · simp only [sptLookup, if_neg hz, if_neg he] at h
          rw [sptInsert]
          simp only [if_neg hz, if_neg he, ihr _ h]
  | bs left old right ihl ihr =>
      by_cases hz : key = 0
      · subst key
        simp [sptLookup] at h
        subst old
        rw [sptInsert]
        simp
      · by_cases he : key % 2 = 0
        · simp only [sptLookup, if_neg hz, if_pos he] at h
          rw [sptInsert]
          simp only [if_neg hz, if_pos he, ihl _ h]
        · simp only [sptLookup, if_neg hz, if_neg he] at h
          rw [sptInsert]
          simp only [if_neg hz, if_neg he, ihr _ h]

end Flapjack
