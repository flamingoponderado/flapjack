import Flapjack.Compiler.Backend.Parmove.InjOnState.Step

namespace Flapjack.Compiler.Backend.Parmove

/-- HOL `steps_inj_on_state` (`parmoveScript.sml:1115`): injectivity on the
endpoint state is preserved by any number of primitive move steps. The only
premises are the source injectivity `injOnState f first` and the reflexive
transitive step relation `Steps first second`; each step is discharged by
`stepInjOnState`, and no global-injectivity, safety or target-result premise is
added. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "steps_inj_on_state"]
theorem stepsInjOnState {α β : Type} (f : Option α → Option β) (first second : State α) :
    injOnState f first ∧ Steps first second → injOnState f second := by
  rintro ⟨h, hsteps⟩
  unfold Steps at hsteps
  induction hsteps with
  | refl => exact h
  | tail _ step ih => exact stepInjOnState f _ _ step ih

end Flapjack.Compiler.Backend.Parmove
