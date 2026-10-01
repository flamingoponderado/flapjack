import Flapjack.HolRef

/-! Literal indexing helpers for the Word-to-Stack stack relation. -/
namespace Flapjack.WordToStackProofs

/-- Descending positions, preserving the input element order. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "index_list_def"]
def indexList {α : Type} : List α → Nat → List (Nat × α)
  | [], _ => []
  | x :: xs, n => (n + xs.length, x) :: indexList xs n

/-- Indexing changes neither the number nor order of source elements. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LENGTH_index_list"]
theorem lengthIndexList {α : Type} (xs : List α) (n : Nat) :
    (indexList xs n).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [indexList, List.length_cons, ih]

/-- Physical-register names are the source name divided by two. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "adjust_names_def"]
def adjustNames (n : Nat) : Nat := n / 2

end Flapjack.WordToStackProofs
