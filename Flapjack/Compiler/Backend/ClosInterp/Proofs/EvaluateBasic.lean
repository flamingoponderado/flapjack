import Flapjack.Compiler.Backend.ClosInterp.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact

/-! Elementary closure evaluations used by the interpreter-insertion proof.
These are proof-side lemmas pending review of the evaluator carriers. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.Compiler.Backend.BackendCommon

/-- A closed constant expression evaluates without changing state. -/
theorem evaluate_constant {C F : Type} (trace : Tra) (constant : ClosLang.Const)
    (env : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluate [.op trace (.blockOp (.constant constant)) []] env state =
      (.val [ClosSem.makeConst constant], state) := by
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock]

/-- A nullary constructor evaluates to its corresponding block. -/
theorem evaluate_cons_nil {C F : Type} (trace : Tra) (tag : Nat)
    (env : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluate [.op trace (.blockOp (.cons tag)) []] env state =
      (.val [.block tag []], state) := by
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock]

/-- In related states, global zero supplies the installed interpreter. -/
theorem evaluate_global_zero {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel source target) (trace : Tra) (env : List ClosSem.Value) (clock : Nat) :
    ClosSem.evaluate [.op trace (.globOp (.global 0)) []] env { target with clock := clock } =
      (.val [.closure none [] [] 1 closInterpreter], { target with clock := clock }) := by
  have globals : target.globals.head? = some (some (.closure none [] [] 1 closInterpreter)) := by
    rw [← related.1.2.2.2.2.2.2.2.1]
    exact related.2
  cases h : target.globals with
  | nil => simp [h] at globals
  | cons first rest =>
    simp [h] at globals
    simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyGlobal,
      ClosSem.getGlobal, globals]

end Flapjack.Compiler.Backend.ClosInterp
