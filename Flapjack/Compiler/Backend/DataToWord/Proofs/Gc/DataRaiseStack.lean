module

public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateStackLocalsSwap
public import Flapjack.Compiler.Backend.Semantics.DataProps.JumpPush
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
/-- Raising across a non-handler frame strictly shortens the original stack. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "eval_exc_stack_shorter"]
theorem evaluate_raise_stackShorter {C F : Type} (c : DataLang.Prog) (ys : List DataSem.Value)
    (ss : Option Nat) (x : Spt DataSem.Value) (s r : DataSem.State C F) (a : DataSem.Value)
    (run : DataSem.evaluate c (DataSem.callEnv ys ss (DataSem.pushEnv x false (DataSem.decClock s))) =
      (some (.err (.raise a)), r)) : r.stack.length < s.stack.length := by
  have post := DataProps.evaluate_stack_swap c (DataSem.callEnv ys ss (DataSem.pushEnv x false (DataSem.decClock s)))
  rw [run] at post
  obtain ⟨s2, jump, localsEq, stackEq, handlerEq, transport⟩ := post
  obtain ⟨orig, origJump, sameStack, sameHandler, sameLocals⟩ :=
    DataSem.jumpExc_callEnv_push_noHandler_inv_locals s s2 x ys ss jump
  obtain ⟨inside, n, env, size, xs, suffix, origEq⟩ := DataSem.jumpExcImp s orig origJump
  have bound : (wordSemLastN (s.handler + 1) s.stack).length ≤ s.stack.length := by
    simpa [wordSemLastN] using Nat.min_le_right (s.handler + 1) s.stack.length
  have lengthEq := congrArg List.length suffix
  simp only [List.length_cons] at lengthEq
  have lt : xs.length < s.stack.length := by omega
  rw [origEq] at sameStack
  rw [← stackEq, sameStack]
  exact lt

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
