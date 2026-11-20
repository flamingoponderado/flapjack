module

public import Flapjack.Misc.Sptree.FromList
public import Flapjack.Misc.Sptree.FromList2

@[expose] public section

/-! List-to-tree append facts used by the data-to-word GC proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- The fold counter is determined by the initial counter, list length, and
step. This proof factors the original fold-length argument. -/
private theorem foldIndex {α : Type} (xs : List α) (k d : Nat) (l : Spt α) :
    (xs.foldl (fun (p : Nat × Spt α) a => (p.1 + d, sptInsert p.1 a p.2)) (k, l)).1 =
      xs.length * d + k := by
  induction xs generalizing k l with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons, ih, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A successful fold exposes the final counter. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "FOLDL_LENGTH_LEMMA"]
theorem foldl_length_lemma {α : Type} (xs : List α) (k : Nat) (l : Spt α) (d q : Nat) (r : Spt α)
    (h : xs.foldl (fun (p : Nat × Spt α) a => (p.1 + d, sptInsert p.1 a p.2)) (k, l) = (q, r)) :
    q = xs.length * d + k := by
  simpa [h] using foldIndex xs k d l

/-- Appending one value inserts it at the next sequential key. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "fromList_SNOC"]
theorem fromList_snoc {α : Type} (xs : List α) (y : α) :
    sptFromList (xs ++ [y]) = sptInsert xs.length y (sptFromList xs) := by
  simp only [sptFromList, List.foldl_append, List.foldl_cons, List.foldl_nil,
    foldIndex, Nat.mul_one, Nat.add_zero]

/-- Appending one value inserts it at the next even key. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "fromList2_SNOC"]
theorem fromList2_snoc {α : Type} (xs : List α) (y : α) :
    sptFromList2 (xs ++ [y]) = sptInsert (2 * xs.length) y (sptFromList2 xs) := by
  simp only [sptFromList2, List.foldl_append, List.foldl_cons, List.foldl_nil,
    foldIndex, Nat.mul_comm, Nat.add_zero]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
