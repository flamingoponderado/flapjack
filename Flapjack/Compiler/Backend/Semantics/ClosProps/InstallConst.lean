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

/-- A binding preserves the arity bound when its bindings and body do. -/
theorem evaluate_let_const_step {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (env : List ClosSem.Value)
    (state : State C F)
    (bindingsIH : (evaluate bindings env state).2.maxApp = state.maxApp)
    (bodyIH : ∀ (bodyEnv : List ClosSem.Value) (start : State C F),
      start.clock ≤ state.clock → (evaluate [body] bodyEnv start).2.maxApp = start.maxApp) :
    (evaluate [.let trace bindings body] env state).2.maxApp = state.maxApp := by
  have bound := evaluate_clock_le bindings env state
  rw [evaluate, fixClock_evaluate]
  cases bindingRun : evaluate bindings env state with
  | mk result next =>
    simp only [bindingRun] at bindingsIH bound
    cases result with
    | err error => exact bindingsIH
    | val values => exact (bodyIH (values ++ env) next bound).trans bindingsIH

/-- Raising a value preserves the arity bound whenever its body does. -/
theorem evaluate_raise_const_step {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (state : State C F)
    (bodyIH : (evaluate [body] env state).2.maxApp = state.maxApp) :
    (evaluate [.raise trace body] env state).2.maxApp = state.maxApp := by
  rw [evaluate]
  cases run : evaluate [body] env state with
  | mk result next =>
    rw [run] at bodyIH
    cases result <;> exact bodyIH

/-- A tick preserves the arity bound, including the timeout case. -/
theorem evaluate_tick_const_step {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (state : State C F)
    (bodyIH : ∀ (start : State C F), start.clock < state.clock →
      (evaluate [body] env start).2.maxApp = start.maxApp) :
    (evaluate [.tick trace body] env state).2.maxApp = state.maxApp := by
  rw [evaluate]
  split
  · rfl
  · have smaller : (decClock 1 state).clock < state.clock := by simp [decClock]; omega
    simpa [decClock] using bodyIH (decClock 1 state) smaller

/-- Recursive closure binding preserves the arity bound if its body does. -/
theorem evaluate_letrec_const_step {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (env : List ClosSem.Value) (state : State C F)
    (bodyIH : ∀ bodyEnv : List ClosSem.Value, (evaluate [body] bodyEnv state).2.maxApp = state.maxApp) :
    (evaluate [.letrec names location selected functions body] env state).2.maxApp = state.maxApp := by
  rw [evaluate.eq_def]
  dsimp only
  repeat' split
  all_goals try rfl
  all_goals exact bodyIH _

/-- A handler preserves the arity bound through both evaluation stages. -/
theorem evaluate_handle_const_step {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (env : List ClosSem.Value) (state : State C F)
    (bodyIH : (evaluate [body] env state).2.maxApp = state.maxApp)
    (handlerIH : ∀ (value : ClosSem.Value) (start : State C F), start.clock ≤ state.clock →
      (evaluate [handler] (value :: env) start).2.maxApp = start.maxApp) :
    (evaluate [.handle trace body handler] env state).2.maxApp = state.maxApp := by
  have bound := evaluate_clock_le [body] env state
  rw [evaluate, fixClock_evaluate]
  cases bodyRun : evaluate [body] env state with
  | mk result next =>
    simp only [bodyRun] at bodyIH bound
    cases result with
    | val values => exact bodyIH
    | err error =>
      cases error with
      | abort reason => exact bodyIH
      | raise value => exact (handlerIH value next bound).trans bodyIH

/-- A conditional preserves the arity bound through its test and selected branch. -/
theorem evaluate_if_const_step {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (env : List ClosSem.Value) (state : State C F)
    (conditionIH : (evaluate [condition] env state).2.maxApp = state.maxApp)
    (branchIH : ∀ (choice : Bool) (start : State C F), start.clock ≤ state.clock →
      (evaluate [if choice then yes else no] env start).2.maxApp = start.maxApp) :
    (evaluate [.ifThenElse trace condition yes no] env state).2.maxApp = state.maxApp := by
  have bound := evaluate_clock_le [condition] env state
  rw [evaluate, fixClock_evaluate]
  cases testRun : evaluate [condition] env state with
  | mk result next =>
    simp only [testRun] at conditionIH bound
    cases result with
    | err error => exact conditionIH
    | val values =>
      dsimp only
      split
      · exact conditionIH
      · exact (branchIH true next bound).trans conditionIH
      · exact (branchIH false next bound).trans conditionIH

/-- A direct call preserves the arity bound when its arguments and called body do. -/
theorem evaluate_call_const_step {C F : Type} (trace : BackendCommon.Tra)
    (ticks location : Nat) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : State C F)
    (argsIH : (evaluate args env state).2.maxApp = state.maxApp)
    (bodyIH : ∀ (body : ClosLang.Exp) (bodyEnv : List ClosSem.Value) (start : State C F),
      start.clock < state.clock → (evaluate [body] bodyEnv start).2.maxApp = start.maxApp) :
    (evaluate [.call trace ticks location args] env state).2.maxApp = state.maxApp := by
  have bound := evaluate_clock_le args env state
  rw [evaluate, fixClock_evaluate]
  cases argsRun : evaluate args env state with
  | mk result next =>
    simp only [argsRun] at argsIH bound
    cases result with
    | err error => exact argsIH
    | val values =>
      dsimp only
      cases found : findCode location values next.code with
      | none => exact argsIH
      | some entry =>
        obtain ⟨bodyEnv, body⟩ := entry
        dsimp only
        split
        · exact argsIH
        · have smaller : (decClock (ticks + 1) next).clock < state.clock := by simp [decClock]; omega
          exact (bodyIH body bodyEnv (decClock (ticks + 1) next) smaller).trans argsIH

/-- Forcing a thunk preserves the arity bound through its argument and body. -/
theorem evaluate_force_const_step {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : State C F)
    (argsIH : (evaluate args env state).2.maxApp = state.maxApp)
    (forceIH : ∀ (value : ClosSem.Value) (start : State C F), start.clock ≤ state.clock →
      (evaluate [appUnit (.var .none 0)] [value] start).2.maxApp = start.maxApp) :
    (evaluate [.op trace (.thunkOp .forceThunk) args] env state).2.maxApp = state.maxApp := by
  have bound := evaluate_clock_le args env state
  rw [evaluate, fixClock_evaluate]
  cases argsRun : evaluate args env state with
  | mk result next =>
    simp only [argsRun] at argsIH bound
    cases result with
    | err error => exact argsIH
    | val values =>
      dsimp only
      cases thunk : destThunk values next.refs with
      | badRef | notThunk => exact argsIH
      | isThunk status value =>
        cases status with
        | evaluated => exact argsIH
        | notEvaluated =>
          dsimp only
          have invariant := forceIH value next bound
          cases forceRun : evaluate [appUnit (.var .none 0)] [value] next with
          | mk result last =>
            rw [forceRun] at invariant
            cases result with
            | err error => exact invariant.trans argsIH
            | val forced =>
              dsimp only
              cases update : updateThunk values last.refs forced with
              | none => exact invariant.trans argsIH
              | some refs => exact invariant.trans argsIH

/-- Closure application preserves the arity bound through arguments, function,
 and application itself. -/
theorem evaluate_app_const_step {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : State C F)
    (argsIH : (evaluate args env state).2.maxApp = state.maxApp)
    (functionIH : ∀ (start : State C F), start.clock ≤ state.clock →
      (evaluate [function] env start).2.maxApp = start.maxApp)
    (appIH : ∀ (value : ClosSem.Value) (values : List ClosSem.Value) (start : State C F),
      start.clock ≤ state.clock → (evaluateApp location value values start).2.maxApp = start.maxApp) :
    (evaluate [.app trace location function args] env state).2.maxApp = state.maxApp := by
  rw [evaluate]
  split
  · rfl
  · rw [fixClock_evaluate]
    have bound := evaluate_clock_le args env state
    cases argsRun : evaluate args env state with
    | mk result next =>
      simp only [argsRun] at argsIH bound
      cases result with
      | err error => exact argsIH
      | val values =>
        dsimp only
        rw [fixClock_evaluate]
        have fnBound := evaluate_clock_le [function] env next
        have fnConst := functionIH next bound
        cases fnRun : evaluate [function] env next with
        | mk result last =>
          simp only [fnRun] at fnBound fnConst
          cases result with
          | err error => exact fnConst.trans argsIH
          | val functions =>
            exact (appIH _ values last (by omega)).trans (fnConst.trans argsIH)

/-- Evaluation and application preserve the closure arity limit on every
result, including errors. This candidate is untagged until the evaluator and
state carrier have been compared with the HOL source. -/
theorem evaluate_const {C F : Type} :
    (∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value) (state : State C F),
      (evaluate expressions env state).2.maxApp = state.maxApp) ∧
    (∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value) (state : State C F),
      (evaluateApp location function args state).2.maxApp = state.maxApp) := by
  have all : ∀ clock : Nat,
      (∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value) (state : State C F),
        state.clock = clock → (evaluateApp location function args state).2.maxApp = state.maxApp) ∧
      (∀ (weight : Nat) (expressions : List ClosLang.Exp) (env : List ClosSem.Value) (state : State C F),
        state.clock = clock → expsWeight expressions = weight →
        (evaluate expressions env state).2.maxApp = state.maxApp) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value) (state : State C F),
          state.clock = clock → (evaluateApp location function args state).2.maxApp = state.maxApp := by
        intro location function args state stateClock
        apply evaluateApp_const_step location function args state
        · intro body env start smaller
          exact (clockIH start.clock (by omega)).2 (expsWeight [body]) [body] env start rfl rfl
        · intro value remaining start smaller
          exact (clockIH start.clock (by omega)).1 location value remaining start rfl
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value) (state : State C F),
              state.clock ≤ clock → expsWeight expressions < weight →
              (evaluate expressions env state).2.maxApp = state.maxApp := by
            intro expressions env state clockLe weightLt
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions env state rfl rfl
            · exact weightIH (expsWeight expressions) weightLt expressions env state clockEq rfl
          have smaller : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value) (state : State C F),
              state.clock < clock → (evaluate expressions env state).2.maxApp = state.maxApp := by
            intro expressions env state clockLt
            exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions env state rfl rfl
          have appBound : ∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value) (state : State C F),
              state.clock ≤ clock → (evaluateApp location function args state).2.maxApp = state.maxApp := by
            intro location function args state clockLe
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).1 location function args state rfl
            · exact appAll location function args state clockEq
          intro expressions env state stateClock measure
          cases expressions with
          | nil => simp [evaluate]
          | cons first rest =>
            cases rest with
            | cons second tail =>
              have headBound := evaluate_clock_le [first] env state
              have headConst := exprIH [first] env state (by omega) (by simp only [expsWeight] at measure ⊢; omega)
              rw [evaluate, fixClock_evaluate]
              cases headRun : evaluate [first] env state with
              | mk headResult next =>
                simp only [headRun] at headBound headConst
                cases headResult with
                | err error => exact headConst
                | val values =>
                  have tailConst := exprIH (second :: tail) env next (by omega) (by simp only [expsWeight] at measure ⊢; omega)
                  cases tailRun : evaluate (second :: tail) env next with
                  | mk tailResult last =>
                    rw [tailRun] at tailConst
                    cases tailResult <;> exact tailConst.trans headConst
            | nil =>
              cases first with
              | var trace index => rw [evaluate]; split <;> rfl
              | fn name location selected arity body =>
                rw [evaluate.eq_def]; dsimp only; split <;> simp_all
                split <;> simp_all
              | raise trace body =>
                apply evaluate_raise_const_step
                apply exprIH [body] env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | tick trace body =>
                apply evaluate_tick_const_step
                intro start bound
                exact smaller [body] env start (by omega)
              | call trace ticks location args =>
                apply evaluate_call_const_step
                · apply exprIH args env state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro body bodyEnv start bound
                  exact smaller [body] bodyEnv start (by omega)
              | «let» trace bindings body =>
                apply evaluate_let_const_step
                · apply exprIH bindings env state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro bodyEnv start bound
                  apply exprIH [body] bodyEnv start (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | letrec names location selected functions body =>
                apply evaluate_letrec_const_step
                intro bodyEnv
                apply exprIH [body] bodyEnv state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | handle trace body handler =>
                apply evaluate_handle_const_step
                · apply exprIH [body] env state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro value start bound
                  apply exprIH [handler] (value :: env) start (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | ifThenElse trace condition yes no =>
                apply evaluate_if_const_step
                · apply exprIH [condition] env state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro choice start bound
                  cases choice <;> simp only [Bool.false_eq_true, if_false, if_true] <;> apply exprIH _ env start (by omega) <;>
                    simp only [expsWeight, expWeight] at measure ⊢ <;> omega
              | app trace location function args =>
                apply evaluate_app_const_step
                · apply exprIH args env state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro start bound
                  apply exprIH [function] env start (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro value values start bound
                  exact appBound location value values start (by omega)
              | op trace op args =>
                have argsSmaller : expsWeight args < weight := by
                  have h := opWeight_gt trace op args
                  simp only [expsWeight] at measure
                  omega
                have argsConst := exprIH args env state (by omega) argsSmaller
                have ordinary : ∀ op, op ≠ .install → op ≠ .thunkOp .forceThunk →
                    (evaluate [.op trace op args] env state).2.maxApp = state.maxApp := by
                  intro op notInstall notForce
                  exact evaluate_ordinaryOp_const_step trace op args env state notInstall notForce argsConst
                cases op with
                | install =>
                  apply evaluate_install_const_step trace args env state argsConst
                  intro program start bound
                  exact smaller program [] start (by omega)
                | thunkOp operation =>
                  cases operation with
                  | forceThunk =>
                    apply evaluate_force_const_step trace args env state argsConst
                    intro value start bound
                    apply exprIH [appUnit (.var .none 0)] [value] start (by omega)
                    have h := appUnit_var_weight
                    simp only [expsWeight, expWeight] at measure
                    simp only [appUnit, expsWeight, expWeight] at h ⊢
                    omega
                  | allocThunk mode => exact ordinary _ (by simp) (by simp)
                  | updateThunk mode => exact ordinary _ (by simp) (by simp)
                | label index => exact ordinary _ (by simp) (by simp)
                | ffi name => exact ordinary _ (by simp) (by simp)
                | intOp operation => exact ordinary _ (by simp) (by simp)
                | wordOp operation => exact ordinary _ (by simp) (by simp)
                | blockOp operation => exact ordinary _ (by simp) (by simp)
                | globOp operation => exact ordinary _ (by simp) (by simp)
                | memOp operation => exact ordinary _ (by simp) (by simp)
  constructor
  · intro expressions env state
    exact (all state.clock).2 (expsWeight expressions) expressions env state rfl rfl
  · intro location function args state
    exact (all state.clock).1 location function args state rfl

end Flapjack.Compiler.Backend.ClosProps
