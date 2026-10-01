import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign

namespace Flapjack.Compiler.Backend.Parmove

/-- The literal scratch-safety concatenation equivalence. A prefix whose
destinations are all real must leave the suffix scratch-safe as well. No
well-formedness or distinctness premise is required. Source and destination
option carriers remain independently quantified, as in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "not_use_temp_before_assign_append"]
theorem notUseTempBeforeAssignAppend {destination source : Type}
    (first second : List (Option destination × Option source)) :
    notUseTempBeforeAssign (first ++ second) = true ↔
      notUseTempBeforeAssign first = true ∧
        ((∀ move ∈ first, move.1.isSome = true) →
          notUseTempBeforeAssign second = true) := by
  induction first with
  | nil => simp [notUseTempBeforeAssign]
  | cons move first ih =>
      rcases move with ⟨destination, source⟩
      cases destination <;> cases source <;>
        simp [notUseTempBeforeAssign, ih]

end Flapjack.Compiler.Backend.Parmove
