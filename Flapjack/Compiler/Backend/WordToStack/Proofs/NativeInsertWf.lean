import Flapjack.Misc.Sptree.Wf
import Flapjack.Pancake.Semantics.LoopSemStateExact

namespace Flapjack.WordToStackProofs
open Flapjack

/-- Full original preservation by native association-list insertion. Both
lists are arbitrary: empty and unequal lengths retain the native truncation
clauses. The sole original assumption is well-formedness of the input tree. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wf_alist_insert"]
theorem wfAlistInsert {α : Type} (xs : List Nat) (ys : List α) (z : Spt α)
    (hw : sptWf z = true) :
    sptWf (LoopSemStateFiniteExact.sptAlistInsert xs ys z) = true := by
  induction xs generalizing ys with
  | nil => exact hw
  | cons x xs ih =>
      cases ys with
      | nil => exact hw
      | cons y ys => exact sptWfInsert x y _ (ih ys)

/-- Flapjack infrastructure: the actual indexed insertion fold preserves
well-formedness from every starting index and well-formed starting tree.
There is no separate HOL declaration for this generalized induction helper. -/
private theorem foldWf {α : Type} (ls : List α) (start : Nat) (tree : Spt α)
    (hw : sptWf tree = true) :
    sptWf (ls.foldl (fun (acc : Nat × Spt α) value =>
      (acc.1 + 2, sptInsert acc.1 value acc.2)) (start, tree)).2 = true := by
  induction ls generalizing start tree with
  | nil => exact hw
  | cons x xs ih =>
      exact ih (start + 2) (sptInsert start x tree) (sptWfInsert start x tree hw)

/-- Full original local `wf_fromList2`: actual even-key native insertion is
well-formed for every payload type and input list, without any premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wf_fromList2"]
theorem wfFromList2 {α : Type} (ls : List α) : sptWf (sptFromList2 ls) = true := by
  exact foldWf ls 0 .ln rfl

end Flapjack.WordToStackProofs
