import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoInstallPrimitives
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength

/-! No-install invariants for the proof-side closure evaluator. Its evaluator
and state carriers still require HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- Every body in the code store is free of installation. -/
def codeNoInstall (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : Prop :=
  ∀ location arity body, code.lookup location = some (arity, body) → ClosLang.hasInstall body = false

/-- A successful direct code lookup returns safe arguments and a safe body. -/
theorem findCode_noInstall (location : Nat) (args output : List ClosSem.Value)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (argsOk : valuesNoInstall args = true) (codeOk : codeNoInstall code)
    (run : ClosSem.findCode location args code = some (output, body)) :
    valuesNoInstall output = true ∧ ClosLang.hasInstall body = false := by
  unfold ClosSem.findCode at run
  cases found : code.lookup location with
  | none => simp [found] at run
  | some entry =>
    rcases entry with ⟨arity, expression⟩
    by_cases same : args.length = arity
    · simp [found, same] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨argsOk, codeOk location arity expression found⟩
    · simp [found, same] at run

/-- Successful global primitives leave code unchanged. -/
theorem applyGlobal_code {C F : Type} (op : ClosLang.GlobOp) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.applyGlobal op args state = some (value, next)) : next.code = state.code := by
  unfold ClosSem.applyGlobal at run
  repeat' split at run
  all_goals simp_all
  all_goals (rcases run with ⟨_, rfl⟩; rfl)

/-- Successful memory primitives leave code unchanged. -/
theorem applyMemory_code {C F : Type} (op : ClosLang.MemOp) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.applyMemory op args state = some (value, next)) : next.code = state.code := by
  unfold ClosSem.applyMemory at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals try (rcases run with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff])
  all_goals try (rcases h with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff] <;> aesop)
  all_goals aesop

/-- Successful ordinary primitives leave the code store unchanged. -/
theorem doApp_code {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.doApp op args state = .val (value, next)) : next.code = state.code := by
  cases op with
  | globOp operation =>
    cases found : ClosSem.applyGlobal operation args state with
    | none => simp [ClosSem.doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, found] using run
      subst pair
      exact applyGlobal_code operation args state next value found
  | blockOp operation =>
    cases found : ClosSem.applyBlock operation args state with
    | none => simp [ClosSem.doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, found] using run
      subst pair
      rw [applyBlock_state operation args state next value found]
  | memOp operation =>
    cases found : ClosSem.applyMemory operation args state with
    | none => simp [ClosSem.doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, found] using run
      subst pair
      exact applyMemory_code operation args state next value found
  | intOp operation =>
    cases found : ClosSem.applyNumeric (.intOp operation) args state with
    | none => simp [ClosSem.doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, found] using run
      subst pair
      rw [applyNumeric_state (.intOp operation) args state next value found]
  | wordOp operation =>
    cases found : ClosSem.applyNumeric (.wordOp operation) args state with
    | none => simp [ClosSem.doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, found] using run
      subst pair
      rw [applyNumeric_state (.wordOp operation) args state next value found]
  | ffi | thunkOp =>
    simp only [ClosSem.doApp] at run
    repeat' split at run
    all_goals simp_all
    all_goals (rcases run with ⟨_, rfl⟩; rfl)
  | label | install => simp [ClosSem.doApp] at run

/-- Ordinary primitive dispatch never raises a language exception. -/
theorem doApp_not_raise {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state : ClosSem.State C F) (value : ClosSem.Value) :
    ClosSem.doApp op args state ≠ .err (.raise value) := by
  unfold ClosSem.doApp
  repeat' split
  all_goals simp_all
  all_goals split <;> simp_all

/-- The parts of a closure evaluator state relevant to the no-install invariant. -/
def evalStateNoInstall {C F : Type} (state : ClosSem.State C F) : Prop :=
  globalsNoInstall state.globals ∧ refsNoInstall state.refs ∧ codeNoInstall state.code

/-- Closure application preserves no-install values and state, assuming the
called body and any remaining application satisfy the same invariant at a
smaller clock. -/
theorem evaluateApp_noInstall_step {C F : Type} (location : Option Nat) (function : ClosSem.Value)
    (args : List ClosSem.Value) (state next : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (functionOk : valueNoInstall function = true) (argsOk : valuesNoInstall args = true)
    (stateOk : evalStateNoInstall state)
    (bodyIH : ∀ (body : ClosLang.Exp) (env : List ClosSem.Value) (start final : ClosSem.State C F)
      (bodyResult : Result (List ClosSem.Value) ClosSem.Value), start.clock < state.clock →
      ClosLang.hasInstall body = false → valuesNoInstall env = true → evalStateNoInstall start →
      ClosSem.evaluate [body] env start = (bodyResult, final) → resultNoInstall bodyResult ∧ evalStateNoInstall final)
    (appIH : ∀ (function : ClosSem.Value) (remaining : List ClosSem.Value) (start final : ClosSem.State C F)
      (appResult : Result (List ClosSem.Value) ClosSem.Value), start.clock < state.clock →
      valueNoInstall function = true → valuesNoInstall remaining = true → evalStateNoInstall start →
      ClosSem.evaluateApp location function remaining start = (appResult, final) → resultNoInstall appResult ∧ evalStateNoInstall final)
    (run : ClosSem.evaluateApp location function args state = (result, next)) :
    resultNoInstall result ∧ evalStateNoInstall next := by
  cases args with
  | nil =>
    simp [ClosSem.evaluateApp] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨by simp [resultNoInstall, valuesNoInstall, functionOk], stateOk⟩
  | cons first rest =>
    rw [ClosSem.evaluateApp] at run
    cases found : ClosSem.destClosure state.maxApp location function (first :: rest) with
    | none =>
      rw [found] at run
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨trivial, stateOk⟩
    | some kind =>
      have kindOk := destClosure_noInstall state.maxApp location function (first :: rest) kind functionOk argsOk found
      rw [found] at run
      dsimp only at run
      cases kind with
      | partialApp value =>
        dsimp only at kindOk run
        split at run
        · simp at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨trivial, by simpa [evalStateNoInstall] using stateOk⟩
        · simp at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨by simp [resultNoInstall, valuesNoInstall, kindOk], by simpa [evalStateNoInstall, ClosSem.decClock] using stateOk⟩
      | fullApp body bodyEnv remaining =>
        dsimp only at kindOk run
        obtain ⟨bodyOk, envOk, remainingOk⟩ := kindOk
        have remainingLt := ClosSem.destClosure_full_remaining_lt state.maxApp location function (first :: rest)
          bodyEnv remaining body found
        let cost := (first :: rest).length - remaining.length
        have costPositive : 0 < cost := Nat.sub_pos_of_lt remainingLt
        split at run
        · simp at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨trivial, by simpa [evalStateNoInstall] using stateOk⟩
        · rw [ClosSem.fixClock_evaluate] at run
          cases bodyRun : ClosSem.evaluate [body] bodyEnv (ClosSem.decClock cost state) with
          | mk bodyResult bodyNext =>
            have bound : bodyNext.clock ≤ (ClosSem.decClock cost state).clock := by
              have bound := ClosSem.evaluate_clock_le [body] bodyEnv (ClosSem.decClock cost state)
              simpa [bodyRun] using bound
            have smaller : (ClosSem.decClock cost state).clock < state.clock := by simp [ClosSem.decClock]; omega
            have startOk : evalStateNoInstall (ClosSem.decClock cost state) := by
              simpa [evalStateNoInstall, ClosSem.decClock] using stateOk
            obtain ⟨bodyResultOk, bodyNextOk⟩ := bodyIH body bodyEnv _ bodyNext bodyResult smaller bodyOk envOk startOk bodyRun
            rw [bodyRun] at run
            cases bodyResult with
            | err error =>
              simp at run
              rcases run with ⟨rfl, rfl⟩
              exact ⟨bodyResultOk, bodyNextOk⟩
            | val bodyValues =>
              cases bodyValues with
              | nil =>
                simp at run
                rcases run with ⟨rfl, rfl⟩
                exact ⟨bodyResultOk, bodyNextOk⟩
              | cons value tail =>
                cases tail with
                | nil =>
                  dsimp only at run
                  have valueOk : valueNoInstall value = true := by simpa [resultNoInstall, valuesNoInstall] using bodyResultOk
                  exact appIH value remaining bodyNext next result (by omega) valueOk remainingOk bodyNextOk run
                | cons other tail =>
                  simp at run
                  rcases run with ⟨rfl, rfl⟩
                  exact ⟨bodyResultOk, bodyNextOk⟩

/-- Direct calls preserve the invariant when argument evaluation and the
selected code body do. The selected body is checked through the code-store
invariant, and runs at a smaller clock. -/
theorem evaluate_call_noInstall_step {C F : Type} (trace : BackendCommon.Tra)
    (ticks location : Nat) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsIH : ∀ (last : ClosSem.State C F) (argResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env state = (argResult, last) → resultNoInstall argResult ∧ evalStateNoInstall last)
    (bodyIH : ∀ (body : ClosLang.Exp) (bodyEnv : List ClosSem.Value) (start final : ClosSem.State C F)
      (bodyResult : Result (List ClosSem.Value) ClosSem.Value), start.clock < state.clock →
      ClosLang.hasInstall body = false → valuesNoInstall bodyEnv = true → evalStateNoInstall start →
      ClosSem.evaluate [body] bodyEnv start = (bodyResult, final) → resultNoInstall bodyResult ∧ evalStateNoInstall final)
    (run : ClosSem.evaluate [.call trace ticks location args] env state = (result, next)) :
    resultNoInstall result ∧ evalStateNoInstall next := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
  cases argsRun : ClosSem.evaluate args env state with
  | mk argResult last =>
    have bound : last.clock ≤ state.clock := by
      have clock := ClosSem.evaluate_clock_le args env state
      simpa [argsRun] using clock
    rw [argsRun] at run
    obtain ⟨argOk, lastOk⟩ := argsIH last argResult argsRun
    cases argResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨argOk, lastOk⟩
    | val arguments =>
      dsimp only at run
      cases found : ClosSem.findCode location arguments last.code with
      | none =>
        simp [found] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨trivial, lastOk⟩
      | some entry =>
        rcases entry with ⟨bodyEnv, body⟩
        rw [found] at run
        dsimp only at run
        have selectedOk := findCode_noInstall location arguments bodyEnv last.code body argOk lastOk.2.2 found
        split at run
        · simp at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨trivial, by simpa [evalStateNoInstall] using lastOk⟩
        · have smaller : (ClosSem.decClock (ticks + 1) last).clock < state.clock := by
            simp [ClosSem.decClock]; omega
          have startOk : evalStateNoInstall (ClosSem.decClock (ticks + 1) last) := by
            simpa [evalStateNoInstall, ClosSem.decClock] using lastOk
          exact bodyIH body bodyEnv _ next result smaller selectedOk.2 selectedOk.1 startOk run

/-- Forcing a thunk preserves the invariant when evaluating its arguments
and forcing an unevaluated safe thunk do. -/
theorem evaluate_force_noInstall_step {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsIH : ∀ (last : ClosSem.State C F) (argResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env state = (argResult, last) → resultNoInstall argResult ∧ evalStateNoInstall last)
    (forceIH : ∀ (value : ClosSem.Value) (start final : ClosSem.State C F)
      (forceResult : Result (List ClosSem.Value) ClosSem.Value), start.clock ≤ state.clock →
      valueNoInstall value = true → evalStateNoInstall start →
      ClosSem.evaluate [ClosSem.appUnit (.var .none 0)] [value] start = (forceResult, final) →
      resultNoInstall forceResult ∧ evalStateNoInstall final)
    (run : ClosSem.evaluate [.op trace (.thunkOp .forceThunk) args] env state = (result, next)) :
    resultNoInstall result ∧ evalStateNoInstall next := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
  cases argsRun : ClosSem.evaluate args env state with
  | mk argResult last =>
    have bound : last.clock ≤ state.clock := by
      have clock := ClosSem.evaluate_clock_le args env state
      simpa [argsRun] using clock
    rw [argsRun] at run
    obtain ⟨argOk, lastOk⟩ := argsIH last argResult argsRun
    cases argResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨argOk, lastOk⟩
    | val arguments =>
      dsimp only at run
      cases inspected : ClosSem.destThunk arguments last.refs with
      | badRef | notThunk =>
        simp [inspected] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨trivial, lastOk⟩
      | isThunk mode value =>
        have valueOk := destThunk_value_noInstall arguments last.refs mode value lastOk.2.1 inspected
        cases mode with
        | evaluated =>
          simp [inspected] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨by simp [resultNoInstall, valuesNoInstall, valueOk], lastOk⟩
        | notEvaluated =>
          rw [inspected] at run
          dsimp only at run
          cases forceRun : ClosSem.evaluate [ClosSem.appUnit (.var .none 0)] [value] last with
          | mk forceResult final =>
            obtain ⟨forceOk, finalOk⟩ := forceIH value last final forceResult bound valueOk lastOk forceRun
            rw [forceRun] at run
            cases forceResult with
            | err error =>
              simp at run
              rcases run with ⟨rfl, rfl⟩
              exact ⟨forceOk, finalOk⟩
            | val forced =>
              dsimp only at run
              cases updated : ClosSem.updateThunk arguments final.refs forced with
              | none =>
                simp [updated] at run
                rcases run with ⟨rfl, rfl⟩
                exact ⟨trivial, finalOk⟩
              | some refs =>
                simp [updated] at run
                rcases run with ⟨rfl, rfl⟩
                have refsOk := updateThunk_noInstall arguments forced final.refs refs finalOk.2.1 forceOk updated
                exact ⟨forceOk, finalOk.1, refsOk, finalOk.2.2⟩

/-- The ordinary operation case preserves no-install results and state,
assuming the same for evaluation of its argument expressions. -/
theorem evaluate_ordinaryOp_noInstall_step {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ (last : ClosSem.State C F) (argResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env state = (argResult, last) → resultNoInstall argResult ∧ evalStateNoInstall last)
    (run : ClosSem.evaluate [.op trace op args] env state = (result, next)) :
    resultNoInstall result ∧ evalStateNoInstall next := by
  rw [ClosSem.evaluate_ordinaryOp_eq trace op args env state notInstall notForce] at run
  cases argsRun : ClosSem.evaluate args env state with
  | mk argResult last =>
    rw [argsRun] at run
    obtain ⟨argOk, lastOk⟩ := argsIH last argResult argsRun
    cases argResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨argOk, lastOk⟩
    | val arguments =>
      cases appRun : ClosSem.doApp op arguments.reverse last with
      | err error =>
        simp [appRun] at run
        rcases run with ⟨rfl, rfl⟩
        constructor
        · cases error with
          | raise value => exact False.elim (doApp_not_raise op arguments.reverse last value appRun)
          | abort _ => trivial
        · exact lastOk
      | val pair =>
        rcases pair with ⟨value, final⟩
        simp [appRun] at run
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨globalsOk, refsOk, codeOk⟩ := lastOk
        have argumentsOk : valuesNoInstall arguments.reverse = true :=
          (valuesNoInstall_reverse arguments).2 argOk
        obtain ⟨valueOk, finalGlobals, finalRefs⟩ :=
          doApp_noInstall op arguments.reverse last final value argumentsOk globalsOk refsOk appRun
        exact ⟨by simp [resultNoInstall, valuesNoInstall, valueOk],
          finalGlobals, finalRefs, by simpa [doApp_code op arguments.reverse last final value appRun] using codeOk⟩

end Flapjack.Compiler.Backend.ClosInterp
