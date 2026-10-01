import Flapjack.Compiler.Backend.Parmove.StepMapInj
import Flapjack.Compiler.Backend.Parmove.InjOnState.Steps

namespace Flapjack.Compiler.Backend.Parmove

/-- HOL `steps_MAP_INJ` (`parmoveScript.sml:1179`): the primitive move relation
is preserved by `map_state f` along any number of steps, provided the source
endpoint is injective. The only premises are the source injectivity
`injOnState f first` and `Steps first second`; each step keeps injectivity by
`stepInjOnState` and transports by `stepMapInj`. No global-injectivity, safety
or target-result premise is added. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "steps_MAP_INJ"]
theorem stepsMapInj {α β : Type} (f : Option α → Option β) (first second : State α) :
    Steps first second → injOnState f first → Steps (mapState f first) (mapState f second) := by
  intro hsteps hinj
  unfold Steps at hsteps
  induction hsteps with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev step ih =>
      have hb : injOnState f _ := stepsInjOnState f first _ ⟨hinj, hprev⟩
      exact Relation.ReflTransGen.tail ih (stepMapInj f _ _ step hb)

end Flapjack.Compiler.Backend.Parmove
