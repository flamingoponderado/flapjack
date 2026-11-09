import Flapjack.Compiler.Backend.ClosFvs.Proofs.Evaluate

/-! The complete operation case of the closure free-variable simulation. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- The original expression-simulation predicate at a fixed environment and
source state, factored out solely to express the induction hypotheses. -/
def EvalAt {C F : Type} (expressions : List ClosLang.Exp) (env : List Value) (source : State C F) : Prop :=
  ∀ (result : Result (List Value) Value) (next : State C F)
    (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
    evaluate expressions env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
      StateRel source target ∧ CodeRel env.length expressions code →
    ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel next targetNext

namespace OpPort
/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The original operation induction case, including installation and force. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_op {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List Value) (source : State C F)
    (argsIH : EvalAt args env source)
    (installIH : ∀ (values : List Value) (middle : State C F) (program : List ClosLang.Exp)
        (installed : State C F),
      evaluate args env source = (.val values, middle) → op = .install →
      doInstall values.reverse middle = (.val program, installed) → EvalAt program [] installed)
    (forceIH : ∀ (values : List Value) (middle : State C F) (value : Value),
      evaluate args env source = (.val values, middle) → op ≠ .install → op = .thunkOp .forceThunk →
      destThunk values middle.refs = .isThunk .notEvaluated value →
      EvalAt [appUnit (.var .none 0)] [value] middle) :
    EvalAt [.op trace op args] env source := by
  intro result sourceNext targetCode nextEnv target premises
  by_cases install : op = .install
  · subst op
    exact evaluate_remove_fvs_install trace args env source argsIH
      (fun values middle program installed argsRun installRun =>
        installIH values middle program installed argsRun rfl installRun)
      result sourceNext targetCode nextEnv target premises
  · by_cases force : op = .thunkOp .forceThunk
    · subst op
      exact evaluate_remove_fvs_force trace args env source argsIH
        (fun values middle value argsRun thunkRun =>
          forceIH values middle value argsRun (by simp) rfl thunkRun)
        result sourceNext targetCode nextEnv target premises
    · exact evaluate_ordinary_op trace op args env source install force argsIH
        result sourceNext targetCode nextEnv target premises
end OpPort

end Flapjack.Compiler.Backend.ClosFvs
