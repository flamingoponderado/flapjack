module

public import Flapjack.Misc.Sptree.UnionAlgebra

@[expose] public section

/-! Sparse-tree construction from concatenated association lists. -/
namespace Flapjack

/-- Building from appended associations is left-biased tree union. -/
@[hol "HOL/src/finite_maps/sptreeScript.sml" "fromAList_append"]
theorem sptFromAList_append {α : Type} (left right : List (Nat × α)) :
    sptFromAList (left ++ right) = sptUnion (sptFromAList left) (sptFromAList right) := by
  induction left with
  | nil => simp [sptFromAList, sptUnion]
  | cons entry rest ih =>
    obtain ⟨key, value⟩ := entry
    simp only [List.cons_append, sptFromAList]
    rw [ih, sptInsert_union key value (sptUnion (sptFromAList rest) (sptFromAList right)),
      sptInsert_union key value (sptFromAList rest), sptUnion_assoc]

end Flapjack
