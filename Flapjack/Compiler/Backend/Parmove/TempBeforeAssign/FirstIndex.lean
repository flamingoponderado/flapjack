import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign
import Flapjack.Misc.FindIndex.ShiftZero
import Flapjack.Misc.FindIndex.Append
import Flapjack.Misc.FindIndex.Bounds

namespace Flapjack.Compiler.Backend.Parmove
open Flapjack.Misc

-- HOL equality is classical. The public statement retains arbitrary,
-- independent carrier types without a decidable-equality caller premise.
noncomputable local instance {α : Type} : DecidableEq α := Classical.typeDecidableEq α

/-- Scratch safety is exactly the existence of a strictly earlier first
scratch write whenever a first scratch read exists. Both searches start at
zero, and their optional first indices are preserved. Independent destination
and source carriers and arbitrary move lists are retained, without validity,
distinctness or scratch-success assumptions. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "not_use_temp_before_assign_thm"]
theorem notUseTempBeforeAssignFirstIndex {destination source : Type}
    (moves : List (Option destination × Option source)) :
    notUseTempBeforeAssign moves = true ↔
      ∀ i, findIndex none (moves.map Prod.snd) 0 = some i →
        ∃ j, findIndex none (moves.map Prod.fst) 0 = some j ∧ j < i := by
  induction moves with
  | nil => simp [notUseTempBeforeAssign, findIndex]
  | cons move moves ih =>
    rcases move with ⟨destination, source⟩
    cases destination <;> cases source <;>
      simp only [notUseTempBeforeAssign, List.map_cons, findIndex,
        Option.some_ne_none, ↓reduceIte]
    all_goals try simp
    all_goals rw [findIndexShiftZero (moves.map Prod.snd) none 1]
    all_goals try rw [findIndexShiftZero (moves.map Prod.fst) none 1]
    all_goals cases read : findIndex none (moves.map Prod.snd) 0 <;>
      cases write : findIndex none (moves.map Prod.fst) 0 <;>
      simp_all

end Flapjack.Compiler.Backend.Parmove
