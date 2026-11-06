module

public import Flapjack.HolRef

@[expose] public section

/-! Consecutive indexing from the CakeML misc theory. -/
namespace Flapjack

/-- Pair each list element with its index, starting at `offset`. -/
@[simp, hol "cakeml/misc/miscScript.sml" "enumerate_def"]
def enumerate {A : Type} : Nat → List A → List (Nat × A)
  | _, [] => []
  | offset, x :: xs => (offset, x) :: enumerate (offset + 1) xs

end Flapjack
