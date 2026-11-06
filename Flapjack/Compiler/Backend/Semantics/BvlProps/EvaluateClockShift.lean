import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateClock
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyClock

/-! Proof factoring for BVL evaluation clock extension; these helpers have no standalone HOL declarations. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem Flapjack.SemanticPrimitivesHOL

namespace ExtensionCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end ExtensionCarrier

/-- Increase the BVL evaluation clock. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "inc_clock_def"
  (fmap_as_finite_support := [refs])]
def incClock {C F : Type} (extra : Nat) (state : Flapjack.Compiler.Backend.BvlSem.State C F) :
    Flapjack.Compiler.Backend.BvlSem.State C F :=
  { state with clock := state.clock + extra }

/-- Adding clock to a variable evaluation preserves its result. -/
theorem evaluate_var_addClock {C F : Type} (index : Nat)
    (env : List BvlSem.Value) (state next : State C F) (result : Result (List BvlSem.Value) BvlSem.Value) (extra : Nat)
    (run : evaluate [.var index] env state = (result, next)) :
    evaluate [.var index] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases found : env[index]? <;> simp [evaluate, found] at run ⊢ <;> rcases run with ⟨rfl, rfl⟩ <;> simp


/-- Raise case of evaluator clock extension, assuming the operand case. -/
theorem evaluate_raise_addClock {C F : Type} (body : Bvl.Exp)
    (env : List BvlSem.Value) (state next : State C F) (result : Result (List BvlSem.Value) BvlSem.Value) (extra : Nat)
    (ih : ∀ (childResult : Result (List BvlSem.Value) BvlSem.Value) (childNext : State C F),
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


/-- Tick case of evaluator clock extension, assuming its body case. -/
theorem evaluate_tick_addClock {C F : Type} (body : Bvl.Exp)
    (env : List BvlSem.Value) (state next : State C F) (result : Result (List BvlSem.Value) BvlSem.Value) (extra : Nat)
    (ih : ∀ (childResult : Result (List BvlSem.Value) BvlSem.Value) (childNext : State C F),
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


/-- Multi-expression list case of clock extension, assuming the head and tail
cases at their respective intermediate states. -/
theorem evaluate_list_addClock {C F : Type} (first second : Bvl.Exp) (rest : List Bvl.Exp)
    (env : List BvlSem.Value) (state next : State C F) (result : Result (List BvlSem.Value) BvlSem.Value) (extra : Nat)
    (headIH : ∀ (headResult : Result (List BvlSem.Value) BvlSem.Value) (headNext : State C F),
      evaluate [first] env state = (headResult, headNext) →
      headResult ≠ .err (.abort .timeoutError) →
      evaluate [first] env { state with clock := state.clock + extra } =
        (headResult, { headNext with clock := headNext.clock + extra }))
    (tailIH : ∀ (headNext tailNext : State C F) (tailResult : Result (List BvlSem.Value) BvlSem.Value),
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
      have headNotTimeout : Result.err error ≠ (Result.err (.abort .timeoutError) : Result (List BvlSem.Value) BvlSem.Value) := by
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



/-- Let-binding case of clock extension, assuming the bindings and body cases. -/
theorem evaluate_let_addClock {C F : Type} (bindings : List Bvl.Exp) (body : Bvl.Exp) (env : List BvlSem.Value) (state next : State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value) (extra : Nat)
    (bindingsIH : ∀ (bindingResult : Result (List BvlSem.Value) BvlSem.Value) (bindingNext : State C F),
      evaluate bindings env state = (bindingResult, bindingNext) → bindingResult ≠ .err (.abort .timeoutError) →
      evaluate bindings env { state with clock := state.clock + extra } =
        (bindingResult, { bindingNext with clock := bindingNext.clock + extra }))
    (bodyIH : ∀ (values : List BvlSem.Value) (bindingNext final : State C F) (bodyResult : Result (List BvlSem.Value) BvlSem.Value),
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


/-- Handler case of clock extension, assuming its body and handler cases. -/
theorem evaluate_handle_addClock {C F : Type} (body handler : Bvl.Exp) (env : List BvlSem.Value) (state next : State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value) (extra : Nat)
    (bodyIH : ∀ (bodyResult : Result (List BvlSem.Value) BvlSem.Value) (bodyNext : State C F),
      evaluate [body] env state = (bodyResult, bodyNext) → bodyResult ≠ .err (.abort .timeoutError) →
      evaluate [body] env { state with clock := state.clock + extra } =
        (bodyResult, { bodyNext with clock := bodyNext.clock + extra }))
    (handlerIH : ∀ (value : BvlSem.Value) (bodyNext final : State C F) (handlerResult : Result (List BvlSem.Value) BvlSem.Value),
      bodyNext.clock ≤ state.clock → evaluate [handler] (value :: env) bodyNext = (handlerResult, final) →
      handlerResult ≠ .err (.abort .timeoutError) →
      evaluate [handler] (value :: env) { bodyNext with clock := bodyNext.clock + extra } =
        (handlerResult, { final with clock := final.clock + extra }))
    (run : evaluate [.handle body handler] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.handle body handler] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases bodyRun : evaluate [body] env state with
  | mk bodyResult bodyNext =>
    have bound : bodyNext.clock ≤ state.clock := by
      have clock := evaluate_clock_le [body] env state
      simpa [bodyRun] using clock
    rw [evaluate, fixClock_evaluate, bodyRun] at run
    have bodyNotTimeout : bodyResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst bodyResult
      simp at run
      exact notTimeout run.1.symm
    have shiftedBody := bodyIH bodyResult bodyNext bodyRun bodyNotTimeout
    rw [evaluate, fixClock_evaluate, shiftedBody]
    cases bodyResult with
    | val values => simp_all
    | err error =>
      cases error with
      | abort reason => simp_all
      | raise value =>
        have handlerRun : evaluate [handler] (value :: env) bodyNext = (result, next) := by simpa using run
        exact handlerIH value bodyNext next result bound handlerRun notTimeout


/-- Conditional case of clock extension, assuming its condition and both
branch cases. -/
theorem evaluate_if_addClock {C F : Type} (condition yes no : Bvl.Exp) (env : List BvlSem.Value) (state next : State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value) (extra : Nat)
    (conditionIH : ∀ (conditionResult : Result (List BvlSem.Value) BvlSem.Value) (conditionNext : State C F),
      evaluate [condition] env state = (conditionResult, conditionNext) →
      conditionResult ≠ .err (.abort .timeoutError) →
      evaluate [condition] env { state with clock := state.clock + extra } =
        (conditionResult, { conditionNext with clock := conditionNext.clock + extra }))
    (branchIH : ∀ (choice : Bool) (conditionNext final : State C F) (branchResult : Result (List BvlSem.Value) BvlSem.Value),
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
      change (match asBool (@Flapjack.holHd BvlSem.Value ⟨unitValue⟩ values) with
        | none => (.err (.abort .typeError), conditionNext)
        | some true => evaluate [yes] env conditionNext
        | some false => evaluate [no] env conditionNext) = (result, next) at run
      change (match asBool (@Flapjack.holHd BvlSem.Value ⟨unitValue⟩ values) with
        | none => ((Result.err (.abort .typeError) : Result (List BvlSem.Value) BvlSem.Value), { conditionNext with clock := conditionNext.clock + extra })
        | some true => evaluate [yes] env { conditionNext with clock := conditionNext.clock + extra }
        | some false => evaluate [no] env { conditionNext with clock := conditionNext.clock + extra }) = _
      cases found : asBool (@Flapjack.holHd BvlSem.Value ⟨unitValue⟩ values) with
      | none => simp [found] at run ⊢; rcases run with ⟨rfl, rfl⟩; simp
      | some choice =>
        cases choice with
        | false =>
          simp only [found] at run ⊢
          exact branchIH false conditionNext next result bound run notTimeout
        | true =>
          simp only [found] at run ⊢
          exact branchIH true conditionNext next result bound run notTimeout


/-- Direct-call case of clock extension, assuming the argument and selected
body cases. -/
theorem evaluate_call_addClock {C F : Type} (ticks : Nat) (location : Option Nat)
    (args : List Bvl.Exp) (env : List BvlSem.Value) (state next : State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value) (extra : Nat)
    (argsIH : ∀ (argResult : Result (List BvlSem.Value) BvlSem.Value) (argNext : State C F),
      evaluate args env state = (argResult, argNext) → argResult ≠ .err (.abort .timeoutError) →
      evaluate args env { state with clock := state.clock + extra } =
        (argResult, { argNext with clock := argNext.clock + extra }))
    (bodyIH : ∀ (body : Bvl.Exp) (values : List BvlSem.Value) (bodyState bodyNext : State C F)
      (bodyResult : Result (List BvlSem.Value) BvlSem.Value), bodyState.clock < state.clock →
      evaluate [body] values bodyState = (bodyResult, bodyNext) → bodyResult ≠ .err (.abort .timeoutError) →
      evaluate [body] values { bodyState with clock := bodyState.clock + extra } =
        (bodyResult, { bodyNext with clock := bodyNext.clock + extra }))
    (run : evaluate [.call ticks location args] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.call ticks location args] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases argsRun : evaluate args env state with
  | mk argResult argNext =>
    have argBound : argNext.clock ≤ state.clock := by
      have bound := evaluate_clock_le args env state
      simpa [argsRun] using bound
    rw [evaluate, fixClock_evaluate, argsRun] at run
    have argNotTimeout : argResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst argResult
      simp at run
      exact notTimeout run.1.symm
    have shiftedArgs := argsIH argResult argNext argsRun argNotTimeout
    rw [evaluate, fixClock_evaluate, shiftedArgs]
    cases argResult with
    | err error => simp_all
    | val values =>
      cases found : findCode location values argNext.code with
      | none =>
        simp [found] at run ⊢
        rcases run with ⟨rfl, rfl⟩
        simp
      | some selected =>
        obtain ⟨callValues, body⟩ := selected
        by_cases timeout : argNext.clock < ticks + 1
        · simp [found, timeout] at run
          exact (notTimeout run.1.symm).elim
        · have enough : ticks + 1 ≤ argNext.clock := by omega
          have shiftedEnough : ¬ argNext.clock + extra < ticks + 1 := by omega
          have bodyRun : evaluate [body] callValues (decClock (ticks + 1) argNext) = (result, next) := by
            simpa [found, timeout] using run
          have smaller : (decClock (ticks + 1) argNext).clock < state.clock := by
            simp only [decClock]
            omega
          have shiftedBody := bodyIH body callValues (decClock (ticks + 1) argNext) next result
            smaller bodyRun notTimeout
          have clocks : decClock (ticks + 1) { argNext with clock := argNext.clock + extra } =
              { decClock (ticks + 1) argNext with clock := (decClock (ticks + 1) argNext).clock + extra } := by
            simp only [decClock]
            congr 1
            omega
          simpa [found, shiftedEnough, clocks] using shiftedBody


/-- Primitive application case of clock extension, assuming the argument case. -/
theorem evaluate_op_addClock {C F : Type} (op : ClosLang.Op) (args : List Bvl.Exp)
    (env : List BvlSem.Value) (state next : State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value) (extra : Nat)
    (ih : ∀ (argResult : Result (List BvlSem.Value) BvlSem.Value) (argNext : State C F),
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

/-- Forcing a thunk preserves clock extension if its selected body does. -/
theorem evaluate_force_addClock {C F : Type} (location index : Nat)
    (env : List BvlSem.Value) (state next : State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value) (extra : Nat)
    (bodyIH : ∀ (body : Bvl.Exp) (values : List BvlSem.Value) (bodyState bodyNext : State C F)
      (bodyResult : Result (List BvlSem.Value) BvlSem.Value), bodyState.clock < state.clock →
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
  have shifted := bodyIH body args (decClock 1 state) next result smaller run notTimeout
  have clocks : decClock 1 { state with clock := state.clock + extra } =
      { decClock 1 state with clock := (decClock 1 state).clock + extra } := by
    simp only [decClock]
    congr 1
    omega
  simpa [found, nonzero, clocks] using shifted

/-- Non-timeout BVL evaluation is stable under adding clock. -/
theorem evaluate_addClock {C F : Type} (expressions : List Bvl.Exp)
    (env : List BvlSem.Value) (state next : State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value) (extra : Nat)
    (run : evaluate expressions env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate expressions env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  have allRanks : ∀ clock weight : Nat, ∀ (expressions : List Bvl.Exp)
      (env : List BvlSem.Value) (state next : State C F)
      (result : Result (List BvlSem.Value) BvlSem.Value),
      state.clock = clock → expsWeight expressions = weight →
      evaluate expressions env state = (result, next) → result ≠ .err (.abort .timeoutError) →
      ∀ extra, evaluate expressions env { state with clock := state.clock + extra } =
        (result, { next with clock := next.clock + extra }) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expressions : List Bvl.Exp) (env : List BvlSem.Value)
            (state next : State C F) (result : Result (List BvlSem.Value) BvlSem.Value),
            state.clock ≤ clock → expsWeight expressions < weight →
            evaluate expressions env state = (result, next) → result ≠ .err (.abort .timeoutError) →
            ∀ extra, evaluate expressions env { state with clock := state.clock + extra } =
              (result, { next with clock := next.clock + extra }) := by
          intro expressions env state next result clockLe weightLt run notTimeout extra
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (expsWeight expressions) expressions env state next result rfl rfl run notTimeout extra
          · exact weightIH (expsWeight expressions) weightLt expressions env state next result clockEq rfl run notTimeout extra
        have smaller : ∀ (expressions : List Bvl.Exp) (env : List BvlSem.Value)
            (state next : State C F) (result : Result (List BvlSem.Value) BvlSem.Value),
            state.clock < clock → evaluate expressions env state = (result, next) →
            result ≠ .err (.abort .timeoutError) → ∀ extra,
            evaluate expressions env { state with clock := state.clock + extra } =
              (result, { next with clock := next.clock + extra }) := by
          intro expressions env state next result clockLt run notTimeout extra
          exact clockIH state.clock clockLt (expsWeight expressions) expressions env state next result rfl rfl run notTimeout extra
        intro expressions env state next result stateClock measure run notTimeout extra
        cases expressions with
        | nil => simp [evaluate] at run; rcases run with ⟨rfl, rfl⟩; simp [evaluate]
        | cons first rest =>
          cases rest with
          | cons second tail =>
            apply evaluate_list_addClock first second tail env state next result extra ?_ ?_ run notTimeout
            · intro childResult childNext childRun childNotTimeout
              apply exprIH [first] env state childNext childResult (by omega) ?_ childRun childNotTimeout extra
              simp only [expsWeight] at measure ⊢; have := expWeight_pos second; omega
            · intro headNext tailNext tailResult bound tailRun tailNotTimeout
              apply exprIH (second :: tail) env headNext tailNext tailResult (by omega) ?_ tailRun tailNotTimeout extra
              simp only [expsWeight] at measure ⊢; omega
          | nil =>
            cases first with
            | var index => exact evaluate_var_addClock index env state next result extra run
            | raise body =>
              apply evaluate_raise_addClock body env state next result extra ?_ run notTimeout
              intro childResult childNext childRun childNotTimeout
              apply exprIH [body] env state childNext childResult (by omega) ?_ childRun childNotTimeout extra
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | tick body =>
              apply evaluate_tick_addClock body env state next result extra ?_ run notTimeout
              intro childResult childNext childRun childNotTimeout
              by_cases zero : state.clock = 0
              · apply exprIH [body] env (decClock 1 state) childNext childResult (by simp [decClock]; omega) ?_ childRun childNotTimeout extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · apply smaller [body] env (decClock 1 state) childNext childResult ?_ childRun childNotTimeout extra
                simp only [decClock]; omega
            | «let» bindings body =>
              apply evaluate_let_addClock bindings body env state next result extra ?_ ?_ run notTimeout
              · intro childResult childNext childRun childNotTimeout
                apply exprIH bindings env state childNext childResult (by omega) ?_ childRun childNotTimeout extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro values childNext final bodyResult bound bodyRun bodyNotTimeout
                apply exprIH [body] (values ++ env) childNext final bodyResult (by omega) ?_ bodyRun bodyNotTimeout extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | handle body handler =>
              apply evaluate_handle_addClock body handler env state next result extra ?_ ?_ run notTimeout
              · intro childResult childNext childRun childNotTimeout
                apply exprIH [body] env state childNext childResult (by omega) ?_ childRun childNotTimeout extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro value childNext final bodyResult bound bodyRun bodyNotTimeout
                apply exprIH [handler] (value :: env) childNext final bodyResult (by omega) ?_ bodyRun bodyNotTimeout extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | ifThenElse condition yes no =>
              apply evaluate_if_addClock condition yes no env state next result extra ?_ ?_ run notTimeout
              · intro childResult childNext childRun childNotTimeout
                apply exprIH [condition] env state childNext childResult (by omega) ?_ childRun childNotTimeout extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro choice childNext final bodyResult bound bodyRun bodyNotTimeout
                apply exprIH [if choice then yes else no] env childNext final bodyResult (by omega) ?_ bodyRun bodyNotTimeout extra
                cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte,
                  expsWeight, expWeight] at measure ⊢ <;> omega
            | op op args =>
              apply evaluate_op_addClock op args env state next result extra ?_ run notTimeout
              intro childResult childNext childRun childNotTimeout
              apply exprIH args env state childNext childResult (by omega) ?_ childRun childNotTimeout extra
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | call ticks location args =>
              apply evaluate_call_addClock ticks location args env state next result extra ?_ ?_ run notTimeout
              · intro childResult childNext childRun childNotTimeout
                apply exprIH args env state childNext childResult (by omega) ?_ childRun childNotTimeout extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro body values childState childNext childResult bound bodyRun bodyNotTimeout
                exact smaller [body] values childState childNext childResult (by omega) bodyRun bodyNotTimeout extra
            | force location index =>
              apply evaluate_force_addClock location index env state next result extra ?_ run notTimeout
              intro body values childState childNext childResult bound bodyRun bodyNotTimeout
              exact smaller [body] values childState childNext childResult (by omega) bodyRun bodyNotTimeout extra
  exact allRanks state.clock (expsWeight expressions) expressions env state next result rfl rfl run notTimeout extra

/-- A non-timeout evaluation remains unchanged when its clock is increased. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_add_clock"
  (fmap_as_finite_support := [refs])]
theorem evaluateAddClock {C F : Type} (expressions : List Bvl.Exp)
    (env : List BvlSem.Value) (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (next : Flapjack.Compiler.Backend.BvlSem.State C F)
    (h : evaluateTuple (expressions, env, state) = (result, next) ∧
      result ≠ .err (.abort .timeoutError)) :
    ∀ extra, evaluateTuple (expressions, env, incClock extra state) =
      (result, incClock extra next) := by
  intro extra
  exact evaluate_addClock expressions env state next result extra h.1 h.2

end Flapjack.Compiler.Backend.BvlProps
