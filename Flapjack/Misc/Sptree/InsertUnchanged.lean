module

public import Flapjack.Misc.Sptree

@[expose] public section

namespace Flapjack

/-- A present binding is unchanged by reinsertion of the same value.
The HOL statement has no well-formedness premise. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "insert_unchanged"]
theorem sptInsertUnchanged {α : Type} (tree : Spt α) (key : Nat) (value : α)
    (h : sptLookup key tree = some value) :
    sptInsert key value tree = tree := by
  induction tree generalizing key with
  | ln => simp [sptLookup] at h
  | ls old => by_cases hz : key = 0 <;> simp_all [sptLookup, sptInsert]
  | bn left right ihl ihr =>
      by_cases hz : key = 0 <;> by_cases he : key % 2 = 0 <;>
        simp_all [sptLookup, sptInsert]
  | bs left old right ihl ihr =>
      by_cases hz : key = 0 <;> by_cases he : key % 2 = 0 <;>
        simp_all [sptLookup, sptInsert]

end Flapjack
