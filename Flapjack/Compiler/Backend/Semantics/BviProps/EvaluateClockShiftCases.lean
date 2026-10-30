import Flapjack.Compiler.Backend.Semantics.BviProps.ApplyClockShift
import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateClockFull

/-! BVI clock-extension case lemmas. These are Flapjack infrastructure; the BVI evaluator is not yet source-reviewed. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BviSem
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)
open Flapjack.Compiler.Backend.BvlSem (Value unitValue asBool)

/-- Flapjack proof helper for the variable case of clock extension. -/
theorem evaluate_var_addClock {C F : Type} (index : Nat)
    (env : List Value) (state next : BviState C F) (result : BviResult) (extra : Nat)
    (run : evaluate [.var index] env state = (result, next)) :
    evaluate [.var index] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases found : env[index]? <;> simp [evaluate, found] at run ⊢ <;> rcases run with ⟨rfl, rfl⟩ <;> simp


/-- Flapjack proof helper for the raise case of clock extension. -/
theorem evaluate_raise_addClock {C F : Type} (body : Bvi.Exp)
    (env : List Value) (state next : BviState C F) (result : BviResult) (extra : Nat)
    (ih : ∀ (childResult : BviResult) (childNext : BviState C F),
      evaluate [body] env state = (childResult, childNext) →
      childResult ≠ .err (.abort .timeoutError) →
      evaluate [body] env { state with clock := state.clock + extra } =
        (childResult, { childNext with clock := childNext.clock + extra }))
    (run : evaluate [.raise body] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.raise body] env { state with clock := state.clock + extra } =
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


/-- Flapjack proof helper for the tick case of clock extension. -/
theorem evaluate_tick_addClock {C F : Type} (body : Bvi.Exp)
    (env : List Value) (state next : BviState C F) (result : BviResult) (extra : Nat)
    (ih : ∀ (childResult : BviResult) (childNext : BviState C F),
      evaluate [body] env (decClock 1 state) = (childResult, childNext) →
      childResult ≠ .err (.abort .timeoutError) →
      evaluate [body] env { decClock 1 state with clock := (decClock 1 state).clock + extra } =
        (childResult, { childNext with clock := childNext.clock + extra }))
    (run : evaluate [.tick body] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.tick body] env { state with clock := state.clock + extra } =
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


/-- Flapjack proof helper for the expression-list case of clock extension. -/
theorem evaluate_list_addClock {C F : Type} (first second : Bvi.Exp) (rest : List Bvi.Exp)
    (env : List Value) (state next : BviState C F) (result : BviResult) (extra : Nat)
    (headIH : ∀ (headResult : BviResult) (headNext : BviState C F),
      evaluate [first] env state = (headResult, headNext) →
      headResult ≠ .err (.abort .timeoutError) →
      evaluate [first] env { state with clock := state.clock + extra } =
        (headResult, { headNext with clock := headNext.clock + extra }))
    (tailIH : ∀ (headNext tailNext : BviState C F) (tailResult : BviResult),
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
      have headNotTimeout : Result.err error ≠ (Result.err (.abort .timeoutError) : BviResult) := by
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



/-- Flapjack proof helper for the let case of clock extension. -/
theorem evaluate_let_addClock {C F : Type} (bindings : List Bvi.Exp) (body : Bvi.Exp) (env : List Value) (state next : BviState C F)
    (result : BviResult) (extra : Nat)
    (bindingsIH : ∀ (bindingResult : BviResult) (bindingNext : BviState C F),
      evaluate bindings env state = (bindingResult, bindingNext) → bindingResult ≠ .err (.abort .timeoutError) →
      evaluate bindings env { state with clock := state.clock + extra } =
        (bindingResult, { bindingNext with clock := bindingNext.clock + extra }))
    (bodyIH : ∀ (values : List Value) (bindingNext final : BviState C F) (bodyResult : BviResult),
      bindingNext.clock ≤ state.clock → evaluate [body] (values ++ env) bindingNext = (bodyResult, final) →
      bodyResult ≠ .err (.abort .timeoutError) →
      evaluate [body] (values ++ env) { bindingNext with clock := bindingNext.clock + extra } =
        (bodyResult, { final with clock := final.clock + extra }))
    (run : evaluate [.let bindings body] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.let bindings body] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases bindingsRun : evaluate bindings env state with
  | mk bindingResult bindingNext =>
    have bound : bindingNext.clock ≤ state.clock := by
      have clock := evaluate_clock_le bindings env state
      simpa [bindingsRun] using clock
    rw [evaluate, fixClock_evaluate, bindingsRun] at run
    have bindingsNotTimeout : bindingResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst bindingResult
      simp at run
      exact notTimeout run.1.symm
    have shiftedBindings := bindingsIH bindingResult bindingNext bindingsRun bindingsNotTimeout
    rw [evaluate, fixClock_evaluate, shiftedBindings]
    cases bindingResult with
    | err error => simp_all
    | val values =>
      have bodyRun : evaluate [body] (values ++ env) bindingNext = (result, next) := by simpa using run
      exact bodyIH values bindingNext next result bound bodyRun notTimeout


/-- Flapjack proof helper for the conditional case of clock extension. -/
theorem evaluate_if_addClock {C F : Type} (condition yes no : Bvi.Exp) (env : List Value) (state next : BviState C F)
    (result : BviResult) (extra : Nat)
    (conditionIH : ∀ (conditionResult : BviResult) (conditionNext : BviState C F),
      evaluate [condition] env state = (conditionResult, conditionNext) →
      conditionResult ≠ .err (.abort .timeoutError) →
      evaluate [condition] env { state with clock := state.clock + extra } =
        (conditionResult, { conditionNext with clock := conditionNext.clock + extra }))
    (branchIH : ∀ (choice : Bool) (conditionNext final : BviState C F) (branchResult : BviResult),
      conditionNext.clock ≤ state.clock → evaluate [if choice then yes else no] env conditionNext = (branchResult, final) →
      branchResult ≠ .err (.abort .timeoutError) →
      evaluate [if choice then yes else no] env { conditionNext with clock := conditionNext.clock + extra } =
        (branchResult, { final with clock := final.clock + extra }))
    (run : evaluate [.ifThenElse condition yes no] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.ifThenElse condition yes no] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases conditionRun : evaluate [condition] env state with
  | mk conditionResult conditionNext =>
    have bound : conditionNext.clock ≤ state.clock := by
      have clock := evaluate_clock_le [condition] env state
      simpa [conditionRun] using clock
    rw [evaluate, fixClock_evaluate, conditionRun] at run
    have conditionNotTimeout : conditionResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst conditionResult
      simp at run
      exact notTimeout run.1.symm
    have shiftedCondition := conditionIH conditionResult conditionNext conditionRun conditionNotTimeout
    rw [evaluate, fixClock_evaluate, shiftedCondition]
    cases conditionResult with
    | err error => simp_all
    | val values =>
      change (match asBool (@Flapjack.holHd Value ⟨unitValue⟩ values) with
        | none => (.err (.abort .typeError), conditionNext)
        | some true => evaluate [yes] env conditionNext
        | some false => evaluate [no] env conditionNext) = (result, next) at run
      change (match asBool (@Flapjack.holHd Value ⟨unitValue⟩ values) with
        | none => ((Result.err (.abort .typeError) : BviResult), { conditionNext with clock := conditionNext.clock + extra })
        | some true => evaluate [yes] env { conditionNext with clock := conditionNext.clock + extra }
        | some false => evaluate [no] env { conditionNext with clock := conditionNext.clock + extra }) = _
      cases found : asBool (@Flapjack.holHd Value ⟨unitValue⟩ values) with
      | none => simp [found] at run ⊢; rcases run with ⟨rfl, rfl⟩; simp
      | some choice =>
        cases choice with
        | false =>
          simp only [found] at run ⊢
          exact branchIH false conditionNext next result bound run notTimeout
        | true =>
          simp only [found] at run ⊢
          exact branchIH true conditionNext next result bound run notTimeout


/-- Flapjack proof helper for the primitive-operation case of clock extension. -/
theorem evaluate_op_addClock {C F : Type} (op : ClosLang.Op) (args : List Bvi.Exp)
    (env : List Value) (state next : BviState C F)
    (result : BviResult) (extra : Nat)
    (ih : ∀ (argResult : BviResult) (argNext : BviState C F),
      evaluate args env state = (argResult, argNext) → argResult ≠ .err (.abort .timeoutError) →
      evaluate args env { state with clock := state.clock + extra } =
        (argResult, { argNext with clock := argNext.clock + extra }))
    (run : evaluate [.op op args] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.op op args] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases argsRun : evaluate args env state with
  | mk argResult argNext =>
    rw [evaluate, fixClock_evaluate, argsRun] at run
    have argNotTimeout : argResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst argResult
      simp at run
      exact notTimeout run.1.symm
    have shifted := ih argResult argNext argsRun argNotTimeout
    rw [evaluate, fixClock_evaluate, shifted]
    cases argResult with
    | err error => simp_all
    | val values =>
      dsimp only
      rw [doApp_setClock]
      cases appRun : doApp op values.reverse argNext with
      | err error => simp_all [setClockResult]
      | val pair =>
        obtain ⟨value, final⟩ := pair
        have clock := doApp_clock op values.reverse argNext final value appRun
        simp_all [setClockResult]

/-- Flapjack proof helper for the return case of clock extension. -/
theorem evaluate_return_addClock {C F : Type} (args : List Bvi.Exp)
    (env : List Value) (state next : BviState C F) (result : BviResult) (extra : Nat)
    (ih : ∀ (childResult : BviResult) (childNext : BviState C F),
      evaluate args env state = (childResult, childNext) →
      childResult ≠ .err (.abort .timeoutError) →
      evaluate args env { state with clock := state.clock + extra } =
        (childResult, { childNext with clock := childNext.clock + extra }))
    (run : evaluate [.return args] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.return args] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases childRun : evaluate args env state with
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


/-- Flapjack proof helper for the thunk-force case of clock extension. -/
theorem evaluate_force_addClock {C F : Type} (location index : Nat)
    (env : List Value) (state next : BviState C F)
    (result : BviResult) (extra : Nat)
    (bodyIH : ∀ (body : Bvi.Exp) (values : List Value) (bodyState bodyNext : BviState C F)
      (bodyResult : BviResult), bodyState.clock < state.clock →
      evaluate [body] values bodyState = (bodyResult, bodyNext) → bodyResult ≠ .err (.abort .timeoutError) →
      evaluate [body] values { bodyState with clock := bodyState.clock + extra } =
        (bodyResult, { bodyNext with clock := bodyNext.clock + extra }))
    (run : evaluate [.force location index] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.force location index] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  rw [evaluate] at run ⊢
  split at run <;> try simp_all
  split at run <;> try simp_all
  split at run <;> try simp_all
  split at run <;> try simp_all
  rename_i args body found nonzero
  have smaller : (decClock 1 state).clock < state.clock := by simp [decClock]; omega
  have clocks : decClock 1 { state with clock := state.clock + extra } =
      { decClock 1 state with clock := (decClock 1 state).clock + extra } := by
    simp only [decClock]
    congr 1
    omega
  cases bodyRun : evaluate [body] args (decClock 1 state) with
  | mk bodyResult bodyNext =>
    have bodyNotTimeout : bodyResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst bodyResult
      simp [bodyRun] at run
      exact notTimeout run.1.symm
    have shifted := bodyIH body args (decClock 1 state) bodyNext bodyResult smaller bodyRun bodyNotTimeout
    rw [bodyRun] at run
    cases bodyResult with
    | val values =>
      simp only [Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      simp [clocks, shifted]
    | err error =>
      cases error with
      | abort reason =>
        simp only [Prod.mk.injEq] at run
        rcases run with ⟨rfl, rfl⟩
        simp [clocks, shifted]
      | raise payload =>
        cases payload <;> simp only [Prod.mk.injEq] at run <;>
          rcases run with ⟨rfl, rfl⟩ <;> simp [clocks, shifted]

end Flapjack.Compiler.Backend.BviProps
