module

public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateStackLocalsSwap
@[expose] public section

/-! Data exception stack length after installing a handler. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

/-- A raise after a pushed handler restores the original stack length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "eval_push_env_T_Raise_IMP_stack_length"]
theorem evaluate_pushEnv_raise_stackLength {C F : Type} (p : DataLang.Prog) (ys : List DataSem.Value)
    (ss : Option Nat) (x : Spt DataSem.Value) (s r : DataSem.State C F) (a : DataSem.Value)
    (run : DataSem.evaluate p (DataSem.callEnv ys ss (DataSem.pushEnv x true (DataSem.decClock s))) =
      (some (.err (.raise a)), r)) : r.stack.length = s.stack.length := by
  have post := DataProps.evaluate_stack_swap p (DataSem.callEnv ys ss (DataSem.pushEnv x true (DataSem.decClock s)))
  rw [run] at post
  obtain ⟨s2, jump, localsEq, stackEq, handlerEq, transport⟩ := post
  simp [DataSem.jumpExc, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock] at jump
  subst s2
  simpa [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock] using congrArg List.length stackEq.symm
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
