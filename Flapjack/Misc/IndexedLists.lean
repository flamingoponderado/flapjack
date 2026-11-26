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

end Flapjack
