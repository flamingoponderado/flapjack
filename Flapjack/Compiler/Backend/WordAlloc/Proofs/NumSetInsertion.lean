import Flapjack.Compiler.Backend.WordAlloc.ProgramLiveness
import Flapjack.Misc.Sptree.Wf

namespace Flapjack.WordAlloc

/-- Literal unit-map insertion commutation, retaining the HOL wf premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "wf_insert_swap"]
theorem wfInsertSwap (tree : NumSet) (a c : Nat) (_hw : sptWf tree = true) :
    sptInsert a () (sptInsert c () tree) = sptInsert c () (sptInsert a () tree) := by
  by_cases h : a = c
  · subst c; rfl
  · exact sptInsert_swap a c () () tree h

/-- Source conjunction: numeric-list insertion preserves wf and commutes
with inserting a single name. Equality compares the entire trees. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "numset_list_insert_swap"]
theorem numsetListInsertSwap (names : List Nat) (head : Nat) (live : NumSet)
    (hw : sptWf live = true) :
    sptWf (numsetListInsert names live) = true ∧
      numsetListInsert names (sptInsert head () live) =
        sptInsert head () (numsetListInsert names live) := by
  induction names with
  | nil => exact ⟨hw, rfl⟩
  | cons name names ih =>
      refine ⟨sptWfInsert name () _ ih.1, ?_⟩
      rw [numsetListInsert, ih.2, numsetListInsert]
      exact wfInsertSwap _ name head ih.1

end Flapjack.WordAlloc
