module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Env
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Splitting a stack into its HOL `BUTLASTN` and `LASTN` parts. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- HOL `BUTLASTN` and `LASTN` partition a list for every count. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "BUTLASTN_APPEND_LASTN"]
theorem butlastn_append_lastn {α : Type} (n : Nat) (xs : List α) :
    (xs.reverse.drop n).reverse ++ wordSemLastN n xs = xs := by
  simp [wordSemLastN, ← List.reverse_append]

/-- If related lists have a nonempty source suffix, the target suffix has a
related head and tail. HOL also quantifies two unused independent values. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "LASTN_LIST_REL_LEMMA"]
theorem lastn_list_rel_lemma {α β γ δ : Type} (source : List α) (target : List β)
    (tail : List α) (n : Nat) (_unusedY : γ) (_unusedYs : δ) (head : α) (rel : α → β → Prop)
    (premises : wordSemLastN n source = head :: tail ∧ List.Forall₂ rel source target) :
    ∃ targetHead targetTail, wordSemLastN n target = targetHead :: targetTail ∧
      rel head targetHead ∧ List.Forall₂ rel tail targetTail := by
  have suffix : List.Forall₂ rel (wordSemLastN n source) (wordSemLastN n target) := by
    unfold wordSemLastN
    apply List.forall₂_reverse_iff.mpr
    exact List.forall₂_take n (List.forall₂_reverse_iff.mpr premises.2)
  rw [premises.1] at suffix
  cases targetSuffix : wordSemLastN n target with
  | nil => simp [targetSuffix] at suffix
  | cons targetHead targetTail =>
    rw [targetSuffix] at suffix
    cases suffix with
    | cons related rest => exact ⟨targetHead, targetTail, rfl, related, rest⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
