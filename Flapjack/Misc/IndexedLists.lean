module

public import Flapjack.HolRef

@[expose] public section

/-! Indexed-list operations used by the CakeML compiler proofs. -/
namespace Flapjack

/-- First occurrence of a value, or the list length when it is absent. -/
@[hol "HOL/src/list/src/indexedListsScript.sml" "findi_def"]
noncomputable def holFindi {α : Type} (value : α) (values : List α) : Nat := by
  classical
  exact match values with
    | [] => 0
    | head :: tail => if value = head then 0 else 1 + holFindi value tail

/-- Original `NOT_MEM_findi_IFF`: an absent value is found at the list length. -/
@[hol "cakeml/misc/miscScript.sml" "NOT_MEM_findi_IFF"]
theorem holFindi_eq_length_iff {α : Type} (e : α) (l : List α) :
    e ∉ l ↔ holFindi e l = l.length := by
  classical
  induction l with
  | nil => simp [holFindi]
  | cons h t ih =>
    rw [List.mem_cons, List.length_cons]
    simp only [holFindi]
    split
    · rename_i same
      rw [same]
      simp
    · rename_i notSame
      rw [not_or, ih]
      constructor
      · rintro ⟨_, equal⟩
        omega
      · intro equal
        exact ⟨notSame, by omega⟩

/-- Original `NOT_MEM_findi`: an absent value is found at the list length. -/
@[hol "cakeml/misc/miscScript.sml" "NOT_MEM_findi"]
theorem holFindi_of_not_mem {α : Type} (e : α) (l : List α) (absent : e ∉ l) :
    holFindi e l = l.length :=
  Iff.mp (holFindi_eq_length_iff e l) absent

/-- Original `findi_APPEND`: finding in an appended list continues in the tail
exactly when the head part did not find it. -/
@[hol "cakeml/misc/miscScript.sml" "findi_APPEND"]
theorem findiAppend {α : Type} (l1 l2 : List α) (x : α) :
    holFindi x (l1 ++ l2) =
      (let n0 := holFindi x l1
       if n0 = l1.length then n0 + holFindi x l2 else n0) := by
  induction l1 with
  | nil =>
    simp only [List.nil_append, holFindi, List.length_nil]
    split
    · omega
    · rename_i h
      simp at h
  | cons a l1 ih =>
    simp only [List.cons_append, holFindi, List.length_cons]
    split
    · rename_i heq
      rw [if_neg (by omega)]
    · rename_i hne
      rw [ih]
      by_cases h : holFindi x l1 = l1.length
      · rw [if_pos h, if_pos (by omega)]
        omega
      · rw [if_neg h, if_neg (by omega)]

end Flapjack
