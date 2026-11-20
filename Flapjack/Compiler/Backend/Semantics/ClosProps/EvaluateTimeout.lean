module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClockShift
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Events
public import Flapjack.HolRef

@[expose] public section

/-! A timeout result of the closure evaluator leaves the clock at zero. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL

namespace EvaluateTimeoutPort
/-- Canonical closure-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end EvaluateTimeoutPort

/-- A timed-out installation leaves the clock at zero. Flapjack-side helper:
the installation timeout clause is reached only at clock zero. -/
private theorem doInstall_timeout_clock {C F : Type} (values : List ClosSem.Value)
    (state next : ClosSem.State C F)
    (run : ClosSem.doInstall values state = (.err (.abort .timeoutError), next)) :
    next.clock = 0 := by
  classical
  unfold ClosSem.doInstall at run
  repeat' first | split at run | simp_all
  all_goals
    obtain ⟨_, rfl⟩ := run
    rfl

/-- A timed-out ordinary primitive operation leaves the clock at zero. -/
private theorem evaluate_ordinaryOp_timeout {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (state next : ClosSem.State C F)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argIH : ∀ (argNext : ClosSem.State C F),
      ClosSem.evaluate args env state = (.err (.abort .timeoutError), argNext) →
      argNext.clock = 0)
    (run : ClosSem.evaluate [.op trace op args] env state =
      (.err (.abort .timeoutError), next)) :
    next.clock = 0 := by
  rw [ClosSem.evaluate_ordinaryOp_eq trace op args env state notInstall notForce] at run
  cases argsRun : ClosSem.evaluate args env state with
  | mk argsResult argsNext =>
    rw [argsRun] at run
    cases argsResult with
    | err error =>
      simp only [Prod.mk.injEq, Result.err.injEq] at run
      obtain ⟨heq, rfl⟩ := run
      rw [heq] at argsRun
      exact argIH argsNext argsRun
    | val arguments =>
      dsimp only at run
      cases appRun : ClosSem.doApp op arguments.reverse argsNext with
      | err error =>
        simp only [appRun, Prod.mk.injEq, Result.err.injEq] at run
        obtain ⟨heq, rfl⟩ := run
        rw [heq] at appRun
        exact absurd appRun (ClosSem.doApp_not_timeout op arguments.reverse argsNext)
      | val pair =>
        rcases pair with ⟨value, final⟩
        simp [appRun] at run

/-- A timed-out force-thunk leaves the clock at zero. -/
private theorem evaluate_forceThunk_timeout {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (state next : ClosSem.State C F)
    (argIH : ∀ (argNext : ClosSem.State C F),
      ClosSem.evaluate args env state = (.err (.abort .timeoutError), argNext) →
      argNext.clock = 0)
    (forceIH : ∀ (value : ClosSem.Value) (argNext final : ClosSem.State C F),
      argNext.clock ≤ state.clock →
      ClosSem.evaluate [ClosSem.appUnit (.var .none 0)] [value] argNext =
        (.err (.abort .timeoutError), final) →
      final.clock = 0)
    (run : ClosSem.evaluate [.op trace (.thunkOp .forceThunk) args] env state =
      (.err (.abort .timeoutError), next)) :
    next.clock = 0 := by
  cases argsRun : ClosSem.evaluate args env state with
  | mk argResult argNext =>
    have bound : argNext.clock ≤ state.clock := by
      have clockLe := ClosSem.evaluate_clock_le args env state
      simp only [argsRun] at clockLe
      omega
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, argsRun] at run
    cases argResult with
    | err error =>
      simp only [Prod.mk.injEq, Result.err.injEq] at run
      obtain ⟨heq, rfl⟩ := run
      rw [heq] at argsRun
      exact argIH argNext argsRun
    | val arguments =>
      dsimp only at run
      cases inspected : ClosSem.destThunk arguments argNext.refs with
      | badRef | notThunk => simp [inspected] at run
      | isThunk mode value =>
        cases mode with
        | evaluated => simp [inspected] at run
        | notEvaluated =>
          rw [inspected] at run
          dsimp only at run
          cases forceRun : ClosSem.evaluate [ClosSem.appUnit (.var .none 0)] [value] argNext with
          | mk forceResult final =>
            rw [forceRun] at run
            cases forceResult with
            | err error =>
              simp only [Prod.mk.injEq, Result.err.injEq] at run
              obtain ⟨heq, rfl⟩ := run
              rw [heq] at forceRun
              exact forceIH value argNext final bound forceRun
            | val forced =>
              dsimp only at run
              cases updated : ClosSem.updateThunk arguments final.refs forced with
              | none => simp [updated] at run
              | some refs => simp [updated] at run

/-- A timed-out installation leaves the clock at zero. -/
private theorem evaluate_install_timeout {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (state next : ClosSem.State C F)
    (argIH : ∀ (argNext : ClosSem.State C F),
      ClosSem.evaluate args env state = (.err (.abort .timeoutError), argNext) →
      argNext.clock = 0)
    (programIH : ∀ (program : List ClosLang.Exp) (last final : ClosSem.State C F),
      last.clock < state.clock →
      ClosSem.evaluate program [] last = (.err (.abort .timeoutError), final) →
      final.clock = 0)
    (run : ClosSem.evaluate [.op trace .install args] env state =
      (.err (.abort .timeoutError), next)) :
    next.clock = 0 := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
  cases argsRun : ClosSem.evaluate args env state with
  | mk result last =>
    rw [argsRun] at run
    cases result with
    | err error =>
      simp only [Prod.mk.injEq, Result.err.injEq] at run
      obtain ⟨heq, rfl⟩ := run
      rw [heq] at argsRun
      exact argIH last argsRun
    | val arguments =>
      dsimp only at run
      cases installRun : ClosSem.doInstall arguments.reverse last with
      | mk installResult installedState =>
        rw [installRun] at run
        cases installResult with
        | err error =>
          simp only [Prod.mk.injEq, Result.err.injEq] at run
          obtain ⟨heq, rfl⟩ := run
          rw [heq] at installRun
          exact doInstall_timeout_clock arguments.reverse last installedState installRun
        | val program =>
          dsimp only at run
          have installClock := ClosSem.doInstall_success_clock arguments.reverse last
            installedState program installRun
          have lastLt : installedState.clock < state.clock := by
            have clockLe := ClosSem.evaluate_clock_le args env state
            simp only [argsRun] at clockLe
            omega
          cases programRun : ClosSem.evaluate program [] installedState with
          | mk programResult final =>
            rw [programRun] at run
            cases programResult with
            | err error =>
              simp only [Prod.mk.injEq, Result.err.injEq] at run
              obtain ⟨heq, rfl⟩ := run
              rw [heq] at programRun
              exact programIH program installedState final lastLt programRun
            | val programValues =>
              dsimp only at run
              simp at run

/-- A timed-out evaluation or application leaves the clock at zero. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_timeout_clocks0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateTimeoutClocks0 {C F : Type} :
    (∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
      (state : ClosSem.State C F) (next : ClosSem.State C F),
      ClosSem.evaluate expressions env state = (.err (.abort .timeoutError), next) →
      next.clock = 0) ∧
    (∀ (locopt : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
      (state : ClosSem.State C F) (next : ClosSem.State C F),
      ClosSem.evaluateApp locopt function args state = (.err (.abort .timeoutError), next) →
      next.clock = 0) := by
  have all : ∀ clock : Nat,
      (∀ (locopt : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
        (state next : ClosSem.State C F), state.clock = clock →
        ClosSem.evaluateApp locopt function args state = (.err (.abort .timeoutError), next) →
        next.clock = 0) ∧
      (∀ (weight : Nat) (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
        (state next : ClosSem.State C F), state.clock = clock →
        ClosSem.expsWeight expressions = weight →
        ClosSem.evaluate expressions env state = (.err (.abort .timeoutError), next) →
        next.clock = 0) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ (locopt : Option Nat) (function : ClosSem.Value)
          (args : List ClosSem.Value) (state next : ClosSem.State C F), state.clock = clock →
          ClosSem.evaluateApp locopt function args state = (.err (.abort .timeoutError), next) →
          next.clock = 0 := by
        intro locopt function args state next stateClock run
        cases args with
        | nil => simp [ClosSem.evaluateApp] at run
        | cons first rest =>
          rw [ClosSem.evaluateApp] at run
          cases found : ClosSem.destClosure state.maxApp locopt function (first :: rest) with
          | none =>
            rw [found] at run
            simp [ClosSem.typeError] at run
          | some kind =>
            rw [found] at run
            dsimp only at run
            cases kind with
            | partialApp value =>
              dsimp only at run
              split at run
              · simp only [ClosSem.timeoutError, Prod.mk.injEq] at run
                obtain ⟨_, rfl⟩ := run
                rfl
              · simp at run
            | fullApp body bodyEnv remaining =>
              dsimp only at run
              have remainingLt := ClosSem.destClosure_full_remaining_lt state.maxApp locopt
                function (first :: rest) bodyEnv remaining body found
              let cost := (first :: rest).length - remaining.length
              have costPositive : 0 < cost := Nat.sub_pos_of_lt remainingLt
              split at run
              · simp only [ClosSem.timeoutError, Prod.mk.injEq] at run
                obtain ⟨_, rfl⟩ := run
                rfl
              · rename_i enough
                have smaller : (ClosSem.decClock cost state).clock < state.clock := by
                  simp only [ClosSem.decClock]
                  exact Nat.sub_lt (Nat.lt_of_lt_of_le costPositive (Nat.le_of_not_lt enough))
                    costPositive
                rw [ClosSem.fixClock_evaluate] at run
                cases bodyRun : ClosSem.evaluate [body] bodyEnv
                    (ClosSem.decClock cost state) with
                | mk bodyResult bodyNext =>
                  rw [bodyRun] at run
                  cases bodyResult with
                  | err error =>
                    simp only [Prod.mk.injEq, Result.err.injEq] at run
                    obtain ⟨heq, rfl⟩ := run
                    rw [heq] at bodyRun
                    exact (clockIH (ClosSem.decClock cost state).clock (by omega)).2
                      (ClosSem.expsWeight [body]) [body] bodyEnv
                      (ClosSem.decClock cost state) bodyNext rfl rfl bodyRun
                  | val bodyValues =>
                    cases bodyValues with
                    | nil =>
                      dsimp only at run
                      simp at run
                    | cons value tail =>
                      cases tail with
                      | nil =>
                        dsimp only at run
                        have bodyClock : bodyNext.clock < clock := by
                          have clockLe := ClosSem.evaluate_clock_le [body] bodyEnv
                            (ClosSem.decClock cost state)
                          simp only [bodyRun] at clockLe
                          omega
                        exact (clockIH bodyNext.clock bodyClock).1 locopt value remaining
                          bodyNext next rfl run
                      | cons other more =>
                        dsimp only at run
                        simp at run
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
              (state next : ClosSem.State C F), state.clock ≤ clock →
              ClosSem.expsWeight expressions < weight →
              ClosSem.evaluate expressions env state = (.err (.abort .timeoutError), next) →
              next.clock = 0 := by
            intro expressions env state next clockLe weightLt run
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).2 (ClosSem.expsWeight expressions) expressions
                env state next rfl rfl run
            · exact weightIH (ClosSem.expsWeight expressions) weightLt expressions env state next
                clockEq rfl run
          have smaller : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
              (state next : ClosSem.State C F), state.clock < clock →
              ClosSem.evaluate expressions env state = (.err (.abort .timeoutError), next) →
              next.clock = 0 := by
            intro expressions env state next clockLt run
            exact (clockIH state.clock clockLt).2 (ClosSem.expsWeight expressions) expressions env
              state next rfl rfl run
          have appBound : ∀ (locopt : Option Nat) (function : ClosSem.Value)
              (args : List ClosSem.Value) (state next : ClosSem.State C F),
              state.clock ≤ clock →
              ClosSem.evaluateApp locopt function args state =
                (.err (.abort .timeoutError), next) →
              next.clock = 0 := by
            intro locopt function args state next clockLe run
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).1 locopt function args state next rfl run
            · exact appAll locopt function args state next clockEq run
          intro expressions env state next stateClock measure run
          cases expressions with
          | nil => simp [ClosSem.evaluate] at run
          | cons first rest =>
            cases rest with
            | cons second tail =>
              rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
              cases headRun : ClosSem.evaluate [first] env state with
              | mk headResult headNext =>
                simp only [headRun] at run
                cases headResult with
                | err error =>
                  simp only [Prod.mk.injEq, Result.err.injEq] at run
                  obtain ⟨heq, rfl⟩ := run
                  rw [heq] at headRun
                  exact exprIH [first] env state headNext (by omega) (by
                    simp only [ClosSem.expsWeight] at measure ⊢
                    omega) headRun
                | val headValues =>
                  cases tailRun : ClosSem.evaluate (second :: tail) env headNext with
                  | mk tailResult tailNext =>
                    simp only [tailRun] at run
                    cases tailResult with
                    | err error =>
                      simp only [Prod.mk.injEq, Result.err.injEq] at run
                      obtain ⟨heq, rfl⟩ := run
                      rw [heq] at tailRun
                      have headBound := ClosSem.evaluate_clock_le [first] env state
                      simp only [headRun] at headBound
                      exact exprIH (second :: tail) env headNext tailNext (by omega) (by
                        simp only [ClosSem.expsWeight] at measure ⊢
                        omega) tailRun
                    | val tailValues => simp at run
            | nil =>
              cases first with
              | var trace index =>
                simp [ClosSem.evaluate] at run
                split at run
                all_goals simp_all
              | fn name location selected arity body =>
                rw [ClosSem.evaluate.eq_def] at run
                dsimp only at run
                repeat' split at run
                all_goals simp_all
              | raise trace body =>
                rw [ClosSem.evaluate] at run
                cases bodyRun : ClosSem.evaluate [body] env state with
                | mk bodyResult bodyNext =>
                  rw [bodyRun] at run
                  cases bodyResult with
                  | err error =>
                    simp only [Prod.mk.injEq, Result.err.injEq] at run
                    obtain ⟨heq, rfl⟩ := run
                    rw [heq] at bodyRun
                    exact exprIH [body] env state bodyNext (by omega) (by
                      simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢
                      omega) bodyRun
                  | val bodyValues =>
                    dsimp only at run
                    simp at run
              | tick trace body =>
                rw [ClosSem.evaluate] at run
                split at run
                · simp only [ClosSem.timeoutError, Prod.mk.injEq] at run
                  simp_all
                · exact smaller [body] env (ClosSem.decClock 1 state) next (by
                    simp only [ClosSem.decClock]
                    omega) run
              | op trace op args =>
                have argsLt : ClosSem.expsWeight args < weight := by
                  have bound := ClosSem.opWeight_gt trace op args
                  simp only [ClosSem.expsWeight] at measure ⊢
                  omega
                cases op with
                | install =>
                  exact evaluate_install_timeout trace args env state next
                    (fun argNext argRun => exprIH args env state argNext (by omega) argsLt argRun)
                    (fun program last final lastLt programRun =>
                      (clockIH last.clock (by omega)).2 (ClosSem.expsWeight program) program []
                        last final rfl rfl programRun)
                    run
                | thunkOp operation =>
                  cases operation with
                  | forceThunk =>
                    exact evaluate_forceThunk_timeout trace args env state next
                      (fun argNext argRun => exprIH args env state argNext (by omega) argsLt argRun)
                      (fun value argNext final clockLe forceRun => by
                        rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
                        · exact (clockIH argNext.clock (by omega)).2
                            (ClosSem.expsWeight [ClosSem.appUnit (.var .none 0)])
                            [ClosSem.appUnit (.var .none 0)] [value] argNext final rfl rfl
                            forceRun
                        · have weightLt : ClosSem.expsWeight [ClosSem.appUnit (.var .none 0)] <
                              weight := by
                            have bound := ClosSem.appUnit_var_weight
                            simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure bound ⊢
                            omega
                          exact weightIH (ClosSem.expsWeight [ClosSem.appUnit (.var .none 0)])
                            weightLt [ClosSem.appUnit (.var .none 0)] [value] argNext final
                            (clockEq.trans stateClock) rfl forceRun)
                      run
                  | allocThunk mode =>
                    exact evaluate_ordinaryOp_timeout trace (.thunkOp (.allocThunk mode)) args env
                      state next (by simp) (by simp)
                      (fun argNext argRun => exprIH args env state argNext (by omega) argsLt argRun)
                      run
                  | updateThunk mode =>
                    exact evaluate_ordinaryOp_timeout trace (.thunkOp (.updateThunk mode)) args env
                      state next (by simp) (by simp)
                      (fun argNext argRun => exprIH args env state argNext (by omega) argsLt argRun)
                      run
                | label n =>
                  exact evaluate_ordinaryOp_timeout trace (.label n) args env state next
                    (by simp) (by simp)
                    (fun argNext argRun => exprIH args env state argNext (by omega) argsLt argRun)
                    run
                | ffi name =>
                  exact evaluate_ordinaryOp_timeout trace (.ffi name) args env state next
                    (by simp) (by simp)
                    (fun argNext argRun => exprIH args env state argNext (by omega) argsLt argRun)
                    run
                | intOp op =>
                  exact evaluate_ordinaryOp_timeout trace (.intOp op) args env state next
                    (by simp) (by simp)
                    (fun argNext argRun => exprIH args env state argNext (by omega) argsLt argRun)
                    run
                | wordOp op =>
                  exact evaluate_ordinaryOp_timeout trace (.wordOp op) args env state next
                    (by simp) (by simp)
                    (fun argNext argRun => exprIH args env state argNext (by omega) argsLt argRun)
                    run
                | blockOp op =>
                  exact evaluate_ordinaryOp_timeout trace (.blockOp op) args env state next
                    (by simp) (by simp)
                    (fun argNext argRun => exprIH args env state argNext (by omega) argsLt argRun)
                    run
                | globOp op =>
                  exact evaluate_ordinaryOp_timeout trace (.globOp op) args env state next
                    (by simp) (by simp)
                    (fun argNext argRun => exprIH args env state argNext (by omega) argsLt argRun)
                    run
                | memOp op =>
                  exact evaluate_ordinaryOp_timeout trace (.memOp op) args env state next
                    (by simp) (by simp)
                    (fun argNext argRun => exprIH args env state argNext (by omega) argsLt argRun)
                    run
              | «let» trace bindings body =>
                have bound := ClosSem.evaluate_clock_le bindings env state
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
                cases bindingRun : ClosSem.evaluate bindings env state with
                | mk result last =>
                  simp only [bindingRun] at run bound
                  cases result with
                  | err error =>
                    simp only [Prod.mk.injEq, Result.err.injEq] at run
                    obtain ⟨heq, rfl⟩ := run
                    rw [heq] at bindingRun
                    exact exprIH bindings env state last (by omega) (by
                      simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢
                      omega) bindingRun
                  | val bindingValues =>
                    exact exprIH [body] (bindingValues ++ env) last next (by omega) (by
                      simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢
                      omega) run
              | letrec names location selected functions body =>
                rw [ClosSem.evaluate.eq_def] at run
                dsimp only at run
                split at run
                · split at run
                  · simp at run
                  · exact exprIH [body] _ state next (by omega) (by
                      simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢
                      omega) run
                · simp at run
              | ifThenElse trace condition yes no =>
                have bound := ClosSem.evaluate_clock_le [condition] env state
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
                cases conditionRun : ClosSem.evaluate [condition] env state with
                | mk result last =>
                  simp only [conditionRun] at run bound
                  cases result with
                  | err error =>
                    simp only [Prod.mk.injEq, Result.err.injEq] at run
                    obtain ⟨heq, rfl⟩ := run
                    rw [heq] at conditionRun
                    exact exprIH [condition] env state last (by omega) (by
                      simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢
                      omega) conditionRun
                  | val conditionValues =>
                    dsimp only at run
                    split at run
                    · simp at run
                    · exact exprIH [yes] env last next (by omega) (by
                        simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢
                        omega) run
                    · exact exprIH [no] env last next (by omega) (by
                        simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢
                        omega) run
              | handle trace body handler =>
                have bound := ClosSem.evaluate_clock_le [body] env state
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
                cases bodyRun : ClosSem.evaluate [body] env state with
                | mk result last =>
                  simp only [bodyRun] at run bound
                  cases result with
                  | val bodyValues => simp at run
                  | err error =>
                    cases error with
                    | abort reason =>
                      simp only [Prod.mk.injEq, Result.err.injEq, ErrorResult.abort.injEq] at run
                      obtain ⟨heq, rfl⟩ := run
                      rw [heq] at bodyRun
                      exact exprIH [body] env state last (by omega) (by
                        simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢
                        omega) bodyRun
                    | raise value =>
                      exact exprIH [handler] (value :: env) last next (by omega) (by
                        simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢
                        omega) run
              | call trace ticks location args =>
                have bound := ClosSem.evaluate_clock_le args env state
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
                cases argsRun : ClosSem.evaluate args env state with
                | mk result last =>
                  simp only [argsRun] at run bound
                  cases result with
                  | err error =>
                    simp only [Prod.mk.injEq, Result.err.injEq] at run
                    obtain ⟨heq, rfl⟩ := run
                    rw [heq] at argsRun
                    exact exprIH args env state last (by omega) (by
                      simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢
                      omega) argsRun
                  | val arguments =>
                    dsimp only at run
                    split at run
                    · simp at run
                    · rename_i selected body found
                      split at run
                      · simp only [ClosSem.timeoutError, Prod.mk.injEq] at run
                        obtain ⟨_, rfl⟩ := run
                        rfl
                      · exact smaller [body] selected (ClosSem.decClock (ticks + 1) last) next (by
                          simp only [ClosSem.decClock]
                          omega) run
              | app trace location function args =>
                cases args with
                | nil => simp [ClosSem.evaluate] at run
                | cons first rest =>
                  have argsBound := ClosSem.evaluate_clock_le (first :: rest) env state
                  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
                  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
                  cases argsRun : ClosSem.evaluate (first :: rest) env state with
                  | mk argsResult argsNext =>
                    simp only [argsRun] at run argsBound
                    cases argsResult with
                    | err error =>
                      simp only [Prod.mk.injEq, Result.err.injEq] at run
                      obtain ⟨heq, rfl⟩ := run
                      rw [heq] at argsRun
                      exact exprIH (first :: rest) env state argsNext (by omega) (by
                        simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢
                        omega) argsRun
                    | val arguments =>
                      dsimp only at run
                      rw [ClosSem.fixClock_evaluate] at run
                      have functionBound := ClosSem.evaluate_clock_le [function] env argsNext
                      cases functionRun : ClosSem.evaluate [function] env argsNext with
                      | mk functionResult functionNext =>
                        simp only [functionRun] at run functionBound
                        cases functionResult with
                        | err error =>
                          simp only [Prod.mk.injEq, Result.err.injEq] at run
                          obtain ⟨heq, rfl⟩ := run
                          rw [heq] at functionRun
                          exact exprIH [function] env argsNext functionNext (by omega) (by
                            simp only [ClosSem.expsWeight, ClosSem.expWeight] at measure ⊢
                            omega) functionRun
                        | val functionValues =>
                          change ClosSem.evaluateApp location
                            (@Flapjack.holHd ClosSem.Value ⟨ClosSem.unitValue⟩ functionValues)
                            arguments functionNext = (.err (.abort .timeoutError), next) at run
                          exact appBound location _ arguments functionNext next (by omega) run
  constructor
  · intro expressions env state next run
    exact (all state.clock).2 (ClosSem.expsWeight expressions) expressions env state next rfl rfl
      run
  · intro locopt function args state next run
    exact (all state.clock).1 locopt function args state next rfl run

end Flapjack.Compiler.Backend.ClosProps
