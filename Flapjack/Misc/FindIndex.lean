module

public import Flapjack.HolRef
public import Flapjack.Misc.Option
public import Flapjack.Basis.Pure.MlList.Search

@[expose] public section

namespace Flapjack.Misc

/-- Literal first-match search with an arbitrary starting offset. Equality is
propositional equality; absence returns none without inspecting the offset. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_def"]
def findIndex {α : Type} [DecidableEq α] (target : α) : List α → Nat → Option Nat
  | [], _ => none
  | head :: tail, offset =>
      if head = target then some offset else findIndex target tail (offset + 1)

/-- Original `find_index_APPEND_same`: a found index survives appending. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_APPEND_same"]
theorem findIndex_append_same {α : Type} [DecidableEq α] (l1 : List α) :
    ∀ (n : α) (m : Nat) (i : Nat) (l2 : List α),
      findIndex n l1 m = some i → findIndex n (l1 ++ l2) m = some i := by
  induction l1 with
  | nil =>
    intro n m i l2 h
    cases h
  | cons a t ih =>
    intro n m i l2 h
    simp only [findIndex, List.cons_append] at h ⊢
    split at h
    · simp_all
    · simp_all

/-- Original `find_index_INDEX_FIND`: the search is HOL's `INDEX_FIND` at the
same offset with the equality predicate, keeping the index. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_INDEX_FIND"]
theorem findIndex_eq_holIndexFind {α : Type} [DecidableEq α] (y : α) :
    ∀ (xs : List α) (n : Nat),
      findIndex y xs n =
        (Flapjack.Basis.Pure.MlList.holIndexFind n (fun x => decide (x = y)) xs).map
          Prod.fst := by
  intro xs
  induction xs with
  | nil =>
    intro n
    rfl
  | cons h t ih =>
    intro n
    by_cases hh : h = y
    · simp [findIndex, Flapjack.Basis.Pure.MlList.holIndexFind, hh]
    · simp [findIndex, Flapjack.Basis.Pure.MlList.holIndexFind, hh, ih (n + 1)]

/-- Original `find_index_NOT_MEM`: the search fails exactly on absent elements. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_NOT_MEM"]
theorem findIndex_eq_none {α : Type} [DecidableEq α] (x : α) :
    ∀ (ls : List α) (n : Nat), (x ∉ ls) ↔ findIndex x ls n = none := by
  intro ls
  induction ls with
  | nil =>
    intro n
    simp [findIndex]
  | cons h t ih =>
    intro n
    by_cases hh : h = x
    · simp [findIndex, hh]
    · have hx : x ≠ h := fun hx => hh hx.symm
      simp [findIndex, hh, hx, ih (n + 1)]

/-- Original `THE_find_index_suff`: a property that holds at every offset
below the length holds of the found index. -/
@[hol "cakeml/misc/miscScript.sml" "THE_find_index_suff"]
theorem holThe_findIndex_suff {α : Type} [DecidableEq α] (P : Nat → Bool) (x : α) :
    ∀ (ls : List α) (n : Nat), (∀ m, m < ls.length → P (m + n) = true) →
      x ∈ ls → P (holThe (findIndex x ls n)) = true := by
  intro ls
  induction ls with
  | nil =>
    intro n _ hmem
    simp at hmem
  | cons h t ih =>
    intro n hP hmem
    by_cases hh : h = x
    · simp only [findIndex, if_pos hh]
      rw [holThe]
      simpa using hP 0 (by simp)
    · have ht : x ∈ t := by
        rcases List.mem_cons.mp hmem with hx | hx
        · exact absurd hx.symm hh
        · exact hx
      simp only [findIndex, if_neg hh]
      have hP' : ∀ m, m < t.length → P (m + (n + 1)) = true := by
        intro m hm
        have := hP (m + 1) (by simp [hm])
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      exact ih (n + 1) hP' ht

/-- Original `find_index_ALL_DISTINCT_EL`: in a duplicate-free list the element
    at position `n` is found at `m + n`. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_ALL_DISTINCT_EL"]
theorem findIndex_nodup_getElem {α : Type} [DecidableEq α] (ls : List α) (n m : Nat)
    (hnd : ls.Nodup) (hn : n < ls.length) :
    findIndex ls[n] ls m = some (m + n) := by
  induction ls generalizing n m with
  | nil => simp at hn
  | cons a t ih =>
    cases n with
    | zero =>
      simp [findIndex]
    | succ k =>
      have hk : k < t.length := by simpa using hn
      have hne : a ≠ t[k] := by
        intro hsame
        have hmem : t[k] ∈ t := List.getElem_mem hk
        exact (List.nodup_cons.mp hnd).1 (hsame ▸ hmem)
      have hstep : findIndex t[k] (a :: t) m = findIndex t[k] t (m + 1) := by
        simp only [findIndex]
        rw [if_neg hne]
      simp only [List.getElem_cons_succ]
      rw [hstep, ih k (m + 1) (List.nodup_cons.mp hnd).2 hk]
      exact congrArg some (by omega)

/-- Original `find_index_INDEX_OF`: the search at offset zero is `INDEX_OF`. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_INDEX_OF"]
theorem findIndex_zero_eq_holIndexOf {α : Type} [DecidableEq α] (y : α) (xs : List α) :
    findIndex y xs 0 = Flapjack.Basis.Pure.MlList.holIndexOf y xs := by
  rw [findIndex_eq_holIndexFind]
  rfl

end Flapjack.Misc
