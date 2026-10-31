import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClockShift

/-! Immutable state fields across closure-code installation. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- Installing code preserves the closure arity bound and FFI state, even if
the installation returns an error. This source-shaped candidate remains
untagged while the installation evaluator and state carrier await HOL review. -/
theorem doInstall_const {C F : Type} (values : List ClosSem.Value) (state next : State C F)
    (result : Result (List ClosLang.Exp) ClosSem.Value)
    (run : doInstall values state = (result, next)) :
    next.maxApp = state.maxApp ∧ next.ffi = state.ffi := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals split at run <;> simp_all
  all_goals
    rcases run with ⟨_, rfl⟩
    exact ⟨rfl, rfl⟩

/-- Successful global primitives preserve the arity bound. -/
private theorem applyGlobal_maxApp {C F : Type} (op : ClosLang.GlobOp) (args : List ClosSem.Value)
    (state next : State C F) (value : ClosSem.Value)
    (run : applyGlobal op args state = some (value, next)) : next.maxApp = state.maxApp := by
  unfold applyGlobal at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Successful block primitives preserve the arity bound. -/
private theorem applyBlock_maxApp {C F : Type} (op : ClosLang.BlockOp) (args : List ClosSem.Value)
    (state next : State C F) (value : ClosSem.Value)
    (run : applyBlock op args state = some (value, next)) : next.maxApp = state.maxApp := by
  unfold applyBlock at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- Successful numeric primitives preserve the arity bound. -/
private theorem applyNumeric_maxApp {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state next : State C F) (value : ClosSem.Value)
    (run : applyNumeric op args state = some (value, next)) : next.maxApp = state.maxApp := by
  unfold applyNumeric at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Successful memory primitives preserve the arity bound. -/
private theorem applyMemory_maxApp {C F : Type} (op : ClosLang.MemOp) (args : List ClosSem.Value)
    (state next : State C F) (value : ClosSem.Value)
    (run : applyMemory op args state = some (value, next)) : next.maxApp = state.maxApp := by
  unfold applyMemory at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals try (rcases run with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff])
  all_goals try (rcases h with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff] <;> aesop)
  all_goals aesop

/-- The primitive dispatcher preserves the arity bound on success. This is
the relevant part of the source's primitive-state invariant; the full HOL
result remains untagged until the evaluator and state carrier are reviewed. -/
theorem doApp_maxApp {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state next : State C F) (value : ClosSem.Value)
    (run : doApp op args state = .val (value, next)) : next.maxApp = state.maxApp := by
  cases op with
  | globOp operation =>
    cases h : applyGlobal operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyGlobal_maxApp operation args state next value h
  | blockOp operation =>
    cases h : applyBlock operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyBlock_maxApp operation args state next value h
  | memOp operation =>
    cases h : applyMemory operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyMemory_maxApp operation args state next value h
  | intOp operation =>
    cases h : applyNumeric (.intOp operation) args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyNumeric_maxApp (.intOp operation) args state next value h
  | wordOp operation =>
    cases h : applyNumeric (.wordOp operation) args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, h] using run
      subst pair
      exact applyNumeric_maxApp (.wordOp operation) args state next value h
  | ffi | thunkOp =>
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all
    all_goals aesop
  | label | install => simp [doApp] at run

/-- The ordinary-operation evaluator case preserves the arity bound when its
argument-list induction hypothesis does. -/
theorem evaluate_ordinaryOp_const_step {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : State C F)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : (evaluate args env state).2.maxApp = state.maxApp) :
    (evaluate [.op trace op args] env state).2.maxApp = state.maxApp := by
  rw [evaluate_ordinaryOp_eq trace op args env state notInstall notForce]
  cases argsRun : evaluate args env state with
  | mk result next =>
    rw [argsRun] at argsIH
    cases result with
    | err error => exact argsIH
    | val values =>
      dsimp only
      cases appRun : doApp op values.reverse next with
      | err error => exact argsIH
      | val pair =>
        obtain ⟨value, last⟩ := pair
        exact (doApp_maxApp op values.reverse next last value appRun).trans argsIH

/-- The installation evaluator case preserves the arity bound when the
argument and newly installed program induction hypotheses do. -/
theorem evaluate_install_const_step {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : State C F)
    (argsIH : (evaluate args env state).2.maxApp = state.maxApp)
    (installedIH : ∀ (program : List ClosLang.Exp) (start : State C F),
      start.clock < state.clock → (evaluate program [] start).2.maxApp = start.maxApp) :
    (evaluate [.op trace .install args] env state).2.maxApp = state.maxApp := by
  have bound := evaluate_clock_le args env state
  rw [evaluate, fixClock_evaluate]
  cases argsRun : evaluate args env state with
  | mk result next =>
    simp only [argsRun] at argsIH bound
    cases result with
    | err error => exact argsIH
    | val values =>
      dsimp only
      cases installRun : doInstall values.reverse next with
      | mk installed last =>
        have installConst := doInstall_const values.reverse next last installed installRun
        cases installed with
        | err error => exact installConst.1.trans argsIH
        | val program =>
          dsimp only
          have clock := doInstall_success_clock values.reverse next last program installRun
          have smaller : last.clock < state.clock := by omega
          have bodyConst := installedIH program last smaller
          cases programRun : evaluate program [] last with
          | mk programResult final =>
            rw [programRun] at bodyConst
            cases programResult <;> exact bodyConst.trans (installConst.1.trans argsIH)

/-- One application step preserves the arity bound when its recursive body
and subsequent application do. The hypotheses are the two smaller-clock
induction hypotheses of the source evaluator. This helper is Flapjack-specific
while the complete evaluator theorem is under construction. -/
theorem evaluateApp_const_step {C F : Type} (location : Option Nat) (function : ClosSem.Value)
    (args : List ClosSem.Value) (state : State C F)
    (bodyIH : ∀ (body : ClosLang.Exp) (env : List ClosSem.Value) (start : State C F),
      start.clock < state.clock → (evaluate [body] env start).2.maxApp = start.maxApp)
    (appIH : ∀ (value : ClosSem.Value) (remaining : List ClosSem.Value) (start : State C F),
      start.clock < state.clock → (evaluateApp location value remaining start).2.maxApp = start.maxApp) :
    (evaluateApp location function args state).2.maxApp = state.maxApp := by
  cases args with
  | nil => simp [evaluateApp]
  | cons first restArgs =>
    rw [evaluateApp]
    cases selected : destClosure state.maxApp location function (first :: restArgs) with
    | none => rfl
    | some kind =>
      cases kind with
      | partialApp value =>
        dsimp only
        split <;> simp [decClock]
      | fullApp body env remaining =>
        dsimp only
        have shorter := destClosure_full_remaining_lt state.maxApp location function (first :: restArgs)
          env remaining body selected
        split
        · rfl
        · rename_i enough
          let cost := (first :: restArgs).length - remaining.length
          let start := decClock cost state
          have costPositive : 0 < cost := Nat.sub_pos_of_lt shorter
          have smaller : start.clock < state.clock := by
            dsimp [start, decClock]
            omega
          rw [fixClock_evaluate]
          cases run : evaluate [body] env start with
          | mk result next =>
            have bound : next.clock ≤ start.clock := by
              have h := evaluate_clock_le [body] env start
              simpa [run] using h
            have bodyConst : next.maxApp = state.maxApp := by
              have h := bodyIH body env start smaller
              rw [run] at h
              exact h
            have nextSmaller : next.clock < state.clock := Nat.lt_of_le_of_lt bound smaller
            cases result with
            | err error => exact bodyConst
            | val values =>
              cases values with
              | nil => exact bodyConst
              | cons value values =>
                cases values with
                | nil => exact (appIH value remaining next nextSmaller).trans bodyConst
                | cons other values => exact bodyConst

/-- Once singleton evaluation preserves the arity bound, list sequencing does
too. The singleton premise is the corresponding evaluator induction result. -/
theorem evaluate_list_const_of_singletons {C F : Type}
    (singleton : ∀ (expression : ClosLang.Exp) (env : List ClosSem.Value) (state : State C F),
      (evaluate [expression] env state).2.maxApp = state.maxApp)
    (expressions : List ClosLang.Exp) (env : List ClosSem.Value) (state : State C F) :
    (evaluate expressions env state).2.maxApp = state.maxApp := by
  induction expressions generalizing state with
  | nil => simp [evaluate]
  | cons first rest ih =>
      cases rest with
      | nil => exact singleton first env state
      | cons second tail =>
          rw [evaluate, fixClock_evaluate]
          cases firstRun : evaluate [first] env state with
          | mk result next =>
            have firstConst := singleton first env state
            rw [firstRun] at firstConst
            cases result with
            | err error => exact firstConst
            | val values =>
              have tailConst := ih next
              cases tailRun : evaluate (second :: tail) env next with
              | mk result last =>
                rw [tailRun] at tailConst
                cases result <;> exact tailConst.trans firstConst

end Flapjack.Compiler.Backend.ClosProps
