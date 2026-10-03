import Flapjack.Misc.FindIndex
import Flapjack.Misc.ListEl
namespace Flapjack.Misc
open Flapjack

/-- Full original bounded membership-to-search statement. Repeated values are permitted, with first-match
search and every EL bounded by the original existential witness. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_MEM"]
theorem findIndex_mem {α : Type} [DecidableEq α] [Nonempty α]
    (values : List α) (target : α) (offset : Nat) :
    target ∈ values → ∃ index,
      findIndex target values offset = some (offset+index) ∧
      index < values.length ∧ holEl index values = target := by
  induction values generalizing offset with
  | nil => simp
  | cons head tail ih =>
    intro hm
    by_cases he : head = target
    · refine ⟨0,?_,by simp,?_⟩
      · simp only [findIndex,if_pos he,Nat.add_zero]
      · simpa only [holEl,holHd] using he
    · have ht : target ∈ tail := by
        rcases List.mem_cons.mp hm with h|h
        · exact False.elim (he h.symm)
        · exact h
      obtain ⟨index,hsearch,hbound,hvalue⟩ := ih (offset+1) ht
      refine ⟨index+1,?_,by simpa using hbound,?_⟩
      · simpa only [findIndex,if_neg he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using hsearch
      · simpa only [holEl,List.tail_cons] using hvalue
end Flapjack.Misc
