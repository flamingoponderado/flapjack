import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Step
import Flapjack.Compiler.Backend.Parmove.Invariants.Preservation

namespace Flapjack.Compiler.Backend.Parmove

/-- Full RTC invariant from HOL: retain both well-formedness and scratch safety
of the reversed active/emitted chronology, including zero primitive steps. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "steps_not_use_temp_before_assign"]
theorem stepsNotUseTempBeforeAssign {α : Type} (first second : State α) :
    (wf first ∧ notUseTempBeforeAssign (first.2.1 ++ first.2.2).reverse = true) ∧
      Steps first second →
    wf second ∧ notUseTempBeforeAssign (second.2.1 ++ second.2.2).reverse = true := by
  rintro ⟨⟨valid, safe⟩, transitions⟩
  induction transitions with
  | refl => exact ⟨valid, safe⟩
  | @tail middle last previous step ih =>
      exact ⟨wf_step middle last step ih.1,
        stepNotUseTempBeforeAssign middle last step ih.1 ih.2⟩

end Flapjack.Compiler.Backend.Parmove
