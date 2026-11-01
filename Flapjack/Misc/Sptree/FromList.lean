import Flapjack.Misc.Sptree

/-! Sequential construction of the original sparse-tree carrier. -/
namespace Flapjack

/-- Insert consecutive list elements at keys starting with zero, in order. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "fromList_def"]
def sptFromList {α : Type} (values : List α) : Spt α :=
  (values.foldl (fun (acc : Nat × Spt α) value => (acc.1 + 1, sptInsert acc.1 value acc.2))
    (0, .ln)).2

end Flapjack
