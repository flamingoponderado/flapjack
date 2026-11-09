import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateInstall
import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateForce
import Flapjack.Compiler.Backend.ClosTicks.Proofs.Apply

/-! Complete operation case of the tick-removal evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem

namespace OpPort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The original operation induction case, including installation and force. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks_op {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List Value) (target : State C F)
    (argsIH : EvalAt args env target)
    (installIH : ∀ (values : List Value) (middle : State C F) (program : List ClosLang.Exp)
        (installed : State C F),
      evaluate args env target = (.val values, middle) → op = .install →
      doInstall values.reverse middle = (.val program, installed) → EvalAt program [] installed)
    (forceIH : ∀ (values : List Value) (middle : State C F) (value : Value),
      evaluate args env target = (.val values, middle) → op ≠ .install → op = .thunkOp .forceThunk →
      destThunk values middle.refs = .isThunk .notEvaluated value →
      EvalAt [appUnit (.var .none 0)] [value] middle) :
    EvalAt [.op trace op args] env target := by
  intro result targetNext envSource source sourceCode premises
  by_cases install : op = .install
  · subst op
    exact evaluate_install trace args env target argsIH
      (fun values middle program installed argsRun installRun =>
        installIH values middle program installed argsRun rfl installRun)
      result targetNext envSource source sourceCode premises
  · by_cases force : op = .thunkOp .forceThunk
    · subst op
      exact evaluate_force trace args env target argsIH
        (fun values middle value argsRun thunkRun =>
          forceIH values middle value argsRun (by simp) rfl thunkRun)
        result targetNext envSource source sourceCode premises
    · exact evaluate_ordinary_op trace op args env target install force argsIH
        result targetNext envSource source sourceCode premises
end OpPort

end Flapjack.Compiler.Backend.ClosTicks
