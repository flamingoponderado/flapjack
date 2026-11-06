import Flapjack.Misc.Sptree

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

end Flapjack
