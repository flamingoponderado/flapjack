import Flapjack.Compiler.Backend.Parmove.AllDistinct.Step

namespace Flapjack.Compiler.Backend.Parmove

/-- The complete HOL RTC invariant, including zero steps. Initial distinctness
is the only state premise; neither well-formedness nor scratch safety is added.
All three move lists and the filtering of scratch destinations are retained. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "ALL_DISTINCT_steps"]
theorem allDistinctSteps {α : Type} (first second : State α) :
    (((first.1 ++ first.2.1 ++ first.2.2).map Prod.fst).filter Option.isSome).Nodup ∧
      Steps first second →
    (((second.1 ++ second.2.1 ++ second.2.2).map Prod.fst).filter Option.isSome).Nodup := by
  rintro ⟨distinct, transitions⟩
  induction transitions with
  | refl => exact distinct
  | @tail middle last previous step ih =>
      exact allDistinctStep middle last step ih

end Flapjack.Compiler.Backend.Parmove
