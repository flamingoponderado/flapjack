import Flapjack.Compiler.Backend.Parmove.Steps
import Mathlib.Tactic.SplitIfs

namespace Flapjack.Compiler.Backend.Parmove

/-- Full primitive-step preservation of distinct real destinations, across
pending, active and emitted moves. Scratch destinations are filtered exactly
as in HOL. No well-formedness or initialized-scratch premise is added. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "ALL_DISTINCT_step"]
theorem allDistinctStep {α : Type} (first second : State α) :
    Step first second →
      (((first.1 ++ first.2.1 ++ first.2.2).map Prod.fst).filter Option.isSome).Nodup →
      (((second.1 ++ second.2.1 ++ second.2.2).map Prod.fst).filter Option.isSome).Nodup := by
  intro transition distinct
  cases transition <;>
    simp_all [List.map_append, List.filter_append, List.filter_cons] <;>
    split_ifs at * <;>
    simp_all [List.nodup_append] <;>
    grind

end Flapjack.Compiler.Backend.Parmove
