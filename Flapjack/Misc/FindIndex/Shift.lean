import Flapjack.Misc.FindIndex.ShiftZero
namespace Flapjack.Misc

/-- Full original successful-search shift statement. All offsets and both conclusion families remain generic. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_shift"]
theorem findIndexShift {α : Type} [DecidableEq α] (values : List α)
    (target : α) (offset index : Nat) :
    findIndex target values offset = some index →
    index ≥ offset ∧ ∀ nextOffset,
      findIndex target values nextOffset = some (index-offset+nextOffset) := by
  intro h
  rw [findIndexShiftZero] at h
  cases hz : findIndex target values 0 with
  | none => simp only [hz,Option.map_none] at h; cases h
  | some first =>
    have he : first+offset = index := by
      simpa only [hz,Option.map_some,Option.some.injEq] using h
    constructor
    · omega
    · intro nextOffset
      rw [findIndexShiftZero,hz,Option.map_some]
      congr 1
      omega
end Flapjack.Misc
