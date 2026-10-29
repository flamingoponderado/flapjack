import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyClockShift
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock

/-! Cases of clock extension for the proof-side closure evaluator. The complete
mutual theorem, evaluator, and carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- Adding clock to a variable evaluation preserves its result. -/
theorem evaluate_var_addClock {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (env : List Value) (state next : State C F) (result : Result (List Value) Value) (extra : Nat)
    (run : evaluate [.var trace index] env state = (result, next)) :
    evaluate [.var trace index] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases found : env[index]? <;> simp [evaluate, found] at run ⊢ <;> rcases run with ⟨rfl, rfl⟩ <;> simp

/-- Adding clock to closure creation preserves its result. -/
theorem evaluate_fn_addClock {C F : Type} (trace : Flapjack.AstHOL.VarN) (location : Option Nat)
    (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (env : List Value) (state next : State C F) (result : Result (List Value) Value) (extra : Nat)
    (run : evaluate [.fn trace location selected arity body] env state = (result, next)) :
    evaluate [.fn trace location selected arity body] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  rw [evaluate.eq_def] at run ⊢
  dsimp only at run ⊢
  repeat' split at run <;> simp_all

/-- Raise case of evaluator clock extension, assuming the operand case. -/
theorem evaluate_raise_addClock {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env : List Value) (state next : State C F) (result : Result (List Value) Value) (extra : Nat)
    (ih : ∀ (childResult : Result (List Value) Value) (childNext : State C F),
      evaluate [body] env state = (childResult, childNext) →
      childResult ≠ .err (.abort .timeoutError) →
      evaluate [body] env { state with clock := state.clock + extra } =
        (childResult, { childNext with clock := childNext.clock + extra }))
    (run : evaluate [.raise trace body] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.raise trace body] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases childRun : evaluate [body] env state with
  | mk childResult childNext =>
    have childNotTimeout : childResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst childResult
      simp [evaluate, childRun] at run
      exact notTimeout run.1.symm
    have shifted := ih childResult childNext childRun childNotTimeout
    rw [evaluate, childRun] at run
    rw [evaluate, shifted]
    cases childResult <;> simp_all


/-- Tick case of evaluator clock extension, assuming its body case. -/
theorem evaluate_tick_addClock {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env : List Value) (state next : State C F) (result : Result (List Value) Value) (extra : Nat)
    (ih : ∀ (childResult : Result (List Value) Value) (childNext : State C F),
      evaluate [body] env (decClock 1 state) = (childResult, childNext) →
      childResult ≠ .err (.abort .timeoutError) →
      evaluate [body] env { decClock 1 state with clock := (decClock 1 state).clock + extra } =
        (childResult, { childNext with clock := childNext.clock + extra }))
    (run : evaluate [.tick trace body] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.tick trace body] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  by_cases zero : state.clock = 0
  · simp [evaluate, zero] at run
    exact (notTimeout run.1.symm).elim
  · have shiftedNonzero : state.clock + extra ≠ 0 := by omega
    have childRun : evaluate [body] env (decClock 1 state) = (result, next) := by
      simpa [evaluate, zero] using run
    have shifted := ih result next childRun notTimeout
    have clocks : decClock 1 { state with clock := state.clock + extra } =
        { decClock 1 state with clock := (decClock 1 state).clock + extra } := by
      simp only [decClock]
      congr 1
      omega
    simpa [evaluate, zero, clocks] using shifted


/-- Multi-expression list case of clock extension, assuming the head and tail
cases at their respective intermediate states. -/
theorem evaluate_list_addClock {C F : Type} (first second : ClosLang.Exp) (rest : List ClosLang.Exp)
    (env : List Value) (state next : State C F) (result : Result (List Value) Value) (extra : Nat)
    (headIH : ∀ (headResult : Result (List Value) Value) (headNext : State C F),
      evaluate [first] env state = (headResult, headNext) →
      headResult ≠ .err (.abort .timeoutError) →
      evaluate [first] env { state with clock := state.clock + extra } =
        (headResult, { headNext with clock := headNext.clock + extra }))
    (tailIH : ∀ (headNext tailNext : State C F) (tailResult : Result (List Value) Value),
      headNext.clock ≤ state.clock → evaluate (second :: rest) env headNext = (tailResult, tailNext) →
      tailResult ≠ .err (.abort .timeoutError) →
      evaluate (second :: rest) env { headNext with clock := headNext.clock + extra } =
        (tailResult, { tailNext with clock := tailNext.clock + extra }))
    (run : evaluate (first :: second :: rest) env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate (first :: second :: rest) env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases headRun : evaluate [first] env state with
  | mk headResult headNext =>
    have headBound : headNext.clock ≤ state.clock := by
      have bound := evaluate_clock_le [first] env state
      simpa [headRun] using bound
    rw [evaluate, fixClock_evaluate, headRun] at run
    cases headResult with
    | err error =>
      simp only at run
      have headNotTimeout : Result.err error ≠ (Result.err (.abort .timeoutError) : Result (List Value) Value) := by
        intro bad
        cases run
        exact notTimeout bad
      have shiftedHead := headIH (.err error) headNext headRun headNotTimeout
      rw [evaluate, fixClock_evaluate, shiftedHead]
      cases run
      rfl
    | val values =>
      cases tailRun : evaluate (second :: rest) env headNext with
      | mk tailResult tailNext =>
        rw [tailRun] at run
        have tailNotTimeout : tailResult ≠ .err (.abort .timeoutError) := by
          intro bad
          subst tailResult
          simp at run
          exact notTimeout run.1.symm
        have shiftedHead := headIH (.val values) headNext headRun (by simp)
        have shiftedTail := tailIH headNext tailNext tailResult headBound tailRun tailNotTimeout
        rw [evaluate, fixClock_evaluate, shiftedHead, shiftedTail]
        cases tailResult <;> simp_all


/-- An ordinary primitive evaluation sequences its arguments and dispatcher. -/
theorem evaluate_ordinaryOp_eq {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List Value) (state : State C F)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk) :
    evaluate [.op trace op args] env state =
      match evaluate args env state with
      | (.err error, last) => (.err error, last)
      | (.val values, last) => match doApp op values.reverse last with
        | .err error => (.err error, last)
        | .val (value, final) => (.val [value], final) := by
  rw [evaluate, fixClock_evaluate]
  cases argsRun : evaluate args env state with
  | mk result last =>
    cases result with
    | err error => rfl
    | val values =>
      cases op with
      | install => exact (notInstall rfl).elim
      | thunkOp operation =>
        cases operation with
        | forceThunk => exact (notForce rfl).elim
        | allocThunk mode => rfl
        | updateThunk mode => rfl
      | label | ffi | intOp | wordOp | blockOp | globOp | memOp => rfl

/-- Ordinary operator case of evaluator clock extension, assuming the
argument-list case. -/
theorem evaluate_ordinaryOp_addClock {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List Value) (state next : State C F)
    (result : Result (List Value) Value) (extra : Nat)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (ih : ∀ (argResult : Result (List Value) Value) (argNext : State C F),
      evaluate args env state = (argResult, argNext) → argResult ≠ .err (.abort .timeoutError) →
      evaluate args env { state with clock := state.clock + extra } =
        (argResult, { argNext with clock := argNext.clock + extra }))
    (run : evaluate [.op trace op args] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.op trace op args] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases argsRun : evaluate args env state with
  | mk argResult argNext =>
    rw [evaluate_ordinaryOp_eq trace op args env state notInstall notForce, argsRun] at run
    have argNotTimeout : argResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst argResult
      simp at run
      exact notTimeout run.1.symm
    have shifted := ih argResult argNext argsRun argNotTimeout
    rw [evaluate_ordinaryOp_eq trace op args env _ notInstall notForce, shifted]
    cases argResult with
    | err error => simp_all
    | val values =>
      dsimp only
      rw [doApp_addClock]
      cases appRun : doApp op values.reverse argNext with
      | err error => simp_all [addClockResult]
      | val pair =>
        obtain ⟨value, final⟩ := pair
        simp_all [addClockResult]

end Flapjack.Compiler.Backend.ClosSem
