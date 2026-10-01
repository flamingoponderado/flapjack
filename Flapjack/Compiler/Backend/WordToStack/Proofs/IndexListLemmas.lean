import Flapjack.Compiler.Backend.WordToStack.Proofs.IndexList
import Std.Tactic

namespace Flapjack.WordToStackProofs

/-- Indexing preserves the list of values, without any length or name premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_SND_index_list"]
theorem mapSndIndexList {α : Type} (xs : List α) (k : Nat) :
    (indexList xs k).map Prod.snd = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [indexList, ih]

/-- Source COUNT_LIST is List.range; keys enumerate its reverse plus k. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_FST_index_list"]
theorem mapFstIndexList {α : Type} (xs : List α) (k : Nat) :
    (indexList xs k).map Prod.fst = ((List.range xs.length).map (fun n => k + n)).reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [indexList, List.range_succ, List.reverse_append, ih]

/-- HOL's total EL is rendered by the kernel bounded accessor only under the
source's own i < LENGTH xs guard. The indexed-list bound follows from its
unconditional length theorem; no new bound or default-value premise is added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EL_index_list"]
theorem elIndexList {α : Type} (xs : List α) (i k : Nat) (h : i < xs.length) :
    (indexList xs k)[i]'(by rw [lengthIndexList]; exact h) =
      (k + xs.length - i - 1, xs[i]) := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
      cases i with
      | zero =>
          simp only [indexList, List.getElem_cons_zero, List.length_cons]
          congr 1
      | succ i =>
          have hi : i < xs.length := by simpa using h
          have hr := ih i hi
          simp only [indexList, List.getElem_cons_succ, List.length_cons]
          rw [hr]
          congr 1
          omega

/-- Equivalent source spelling of the same guarded lookup arithmetic. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EL_index_list2"]
theorem elIndexList2 {α : Type} (xs : List α) (i k : Nat) (h : i < xs.length) :
    (indexList xs k)[i]'(by rw [lengthIndexList]; exact h) =
      (k + xs.length - (i + 1), xs[i]) := by
  rw [elIndexList xs i k h]
  congr 1

/-- HOL `MAP_FST_def`: map the key of each pair, leaving the value untouched.
Untagged-target check: fully polymorphic pair-list key mapping, no carrier
translation. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_FST_def"]
def mapFstHOL {α β γ : Type} (f : α → β) (xs : List (α × γ)) : List (β × γ) :=
  xs.map (fun p => (f p.1, p.2))

/-- HOL `MAP_SND_MAP_FST`: `MAP_FST` preserves the value projection for an arbitrary
function and list. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_SND_MAP_FST"]
theorem mapSndMapFstHOL {α β γ : Type} (xs : List (α × γ)) (f : α → β) :
    (mapFstHOL f xs).map Prod.snd = xs.map Prod.snd := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      show ((f x.1, x.2) :: mapFstHOL f xs).map Prod.snd = (x :: xs).map Prod.snd
      rw [List.map_cons, List.map_cons, ih]
end Flapjack.WordToStackProofs
