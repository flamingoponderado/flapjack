import Flapjack.Misc.FindIndex

namespace Flapjack.Misc

/-- Full original successful-search membership law, with arbitrary carrier,
starting offset and returned index. Repeated values are permitted. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_is_MEM"]
theorem findIndex_isMem {α : Type} [DecidableEq α] (target : α)
    (values : List α) (offset index : Nat) :
    findIndex target values offset = some index → target ∈ values := by
  induction values generalizing offset with
  | nil => simp [findIndex]
  | cons head tail ih =>
    intro hs
    by_cases he : head = target
    · exact List.mem_cons.mpr (Or.inl he.symm)
    · have ht : findIndex target tail (offset+1) = some index := by
        simpa only [findIndex, if_neg he] using hs
      exact List.mem_cons.mpr (Or.inr (ih (offset+1) ht))

end Flapjack.Misc
