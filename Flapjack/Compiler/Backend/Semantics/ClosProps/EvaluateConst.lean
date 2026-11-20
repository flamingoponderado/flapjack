module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.InstallConst
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
public import Flapjack.HolRef

@[expose] public section

/-! Preservation of the maximum application arity across evaluation. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL
open Flapjack.HolRef

namespace EvaluateConstPort
/-- Canonical closure-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end EvaluateConstPort

/-- Evaluation and application preserve the maximum application arity. -/
private theorem evaluateConst_both {C F : Type} :
    (∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
      (state next : State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      evaluate expressions env state = (result, next) → next.maxApp = state.maxApp) ∧
    (∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
      (state next : State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      evaluateApp location function args state = (result, next) → next.maxApp = state.maxApp) := by
  have all : ∀ clock : Nat,
      (∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
        (state next : State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
        state.clock = clock → evaluateApp location function args state = (result, next) →
        next.maxApp = state.maxApp) ∧
      (∀ (weight : Nat) (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
        (state next : State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
        state.clock = clock → expsWeight expressions = weight →
        evaluate expressions env state = (result, next) → next.maxApp = state.maxApp) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ (location : Option Nat) (function : ClosSem.Value)
          (args : List ClosSem.Value) (state next : State C F)
          (result : Result (List ClosSem.Value) ClosSem.Value),
          state.clock = clock → evaluateApp location function args state = (result, next) →
          next.maxApp = state.maxApp := by
        intro location function args state next result stateClock run
        cases args with
        | nil =>
          simp only [evaluateApp, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          rfl
        | cons first rest =>
          rw [evaluateApp] at run
          cases found : destClosure state.maxApp location function (first :: rest) with
          | none =>
            rw [found] at run
            simp only [typeError, Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            rfl
          | some kind =>
            rw [found] at run
            dsimp only at run
            cases kind with
            | partialApp value =>
              dsimp only at run
              split at run
              · simp only [timeoutError, Prod.mk.injEq] at run
                obtain ⟨rfl, rfl⟩ := run
                rfl
              · simp only [Prod.mk.injEq] at run
                obtain ⟨rfl, rfl⟩ := run
                rfl
            | fullApp body bodyEnv remaining =>
              dsimp only at run
              have remainingLt := destClosure_full_remaining_lt state.maxApp location function
                (first :: rest) bodyEnv remaining body found
              let cost := (first :: rest).length - remaining.length
              have costPositive : 0 < cost := Nat.sub_pos_of_lt remainingLt
              split at run
              · simp only [timeoutError, Prod.mk.injEq] at run
                obtain ⟨rfl, rfl⟩ := run
                rfl
              · rename_i enough
                have smaller : (decClock cost state).clock < state.clock := by
                  simp only [decClock]
                  exact Nat.sub_lt (Nat.lt_of_lt_of_le costPositive (Nat.le_of_not_lt enough))
                    costPositive
                rw [fixClock_evaluate] at run
                cases bodyRun : evaluate [body] bodyEnv (decClock cost state) with
                | mk bodyResult bodyNext =>
                  have bodyMax : bodyNext.maxApp = state.maxApp := by
                    have inner := (clockIH (decClock cost state).clock (by omega)).2
                      (expsWeight [body]) [body] bodyEnv (decClock cost state) bodyNext bodyResult
                      rfl rfl bodyRun
                    simpa [decClock] using inner
                  rw [bodyRun] at run
                  cases bodyResult with
                  | err error =>
                    dsimp only at run
                    simp only [Prod.mk.injEq] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact bodyMax
                  | val bodyValues =>
                    cases bodyValues with
                    | nil =>
                      dsimp only at run
                      simp only [Prod.mk.injEq] at run
                      obtain ⟨rfl, rfl⟩ := run
                      exact bodyMax
                    | cons value tail =>
                      cases tail with
                      | nil =>
                        dsimp only at run
                        have bodyClock : bodyNext.clock < clock := by
                          have bound := evaluate_clock_le [body] bodyEnv (decClock cost state)
                          simp only [bodyRun] at bound
                          omega
                        exact ((clockIH bodyNext.clock bodyClock).1 location value remaining
                          bodyNext next result rfl run).trans bodyMax
                      | cons other more =>
                        dsimp only at run
                        simp only [Prod.mk.injEq] at run
                        obtain ⟨rfl, rfl⟩ := run
                        exact bodyMax
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
              (state next : State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
              state.clock ≤ clock → expsWeight expressions < weight →
              evaluate expressions env state = (result, next) → next.maxApp = state.maxApp := by
            intro expressions env state next result clockLe weightLt run
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions env
                state next result rfl rfl run
            · exact weightIH (expsWeight expressions) weightLt expressions env state next result
                clockEq rfl run
          have appIH : ∀ (location : Option Nat) (function : ClosSem.Value)
              (args : List ClosSem.Value) (state next : State C F)
              (result : Result (List ClosSem.Value) ClosSem.Value),
              state.clock ≤ clock → evaluateApp location function args state = (result, next) →
              next.maxApp = state.maxApp := by
            intro location function args state next result clockLe run
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).1 location function args state next result rfl run
            · exact appAll location function args state next result clockEq run
          intro expressions env state next result stateClock measure run
          cases expressions with
          | nil =>
            simp only [evaluate, Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            rfl
          | cons first rest =>
            cases rest with
            | cons second tail =>
              have headBound := evaluate_clock_le [first] env state
              rw [evaluate, fixClock_evaluate] at run
              cases headRun : evaluate [first] env state with
              | mk headResult headNext =>
                simp only [headRun] at run headBound
                cases headResult with
                | err error =>
                  simp only [Prod.mk.injEq] at run
                  obtain ⟨rfl, rfl⟩ := run
                  exact exprIH [first] env state headNext (.err error) (by omega) (by
                    simp only [expsWeight] at measure ⊢
                    omega) headRun
                | val headValues =>
                  have headMax : headNext.maxApp = state.maxApp :=
                    exprIH [first] env state headNext (.val headValues) (by omega) (by
                      simp only [expsWeight] at measure ⊢
                      omega) headRun
                  cases tailRun : evaluate (second :: tail) env headNext with
                  | mk tailResult tailNext =>
                    simp only [tailRun] at run
                    cases tailResult with
                    | err error =>
                      simp only [Prod.mk.injEq] at run
                      obtain ⟨rfl, rfl⟩ := run
                      exact (exprIH (second :: tail) env headNext tailNext (.err error)
                        (by omega) (by
                        simp only [expsWeight] at measure ⊢
                        omega) tailRun).trans headMax
                    | val tailValues =>
                      simp only [Prod.mk.injEq] at run
                      obtain ⟨rfl, rfl⟩ := run
                      exact (exprIH (second :: tail) env headNext tailNext (.val tailValues)
                        (by omega) (by
                        simp only [expsWeight] at measure ⊢
                        omega) tailRun).trans headMax
            | nil =>
              cases first with
              | var trace index =>
                rw [evaluate] at run
                cases indexRun : env[index]? with
                | none =>
                  rw [indexRun] at run
                  simp only [typeError, Prod.mk.injEq] at run
                  obtain ⟨rfl, rfl⟩ := run
                  rfl
                | some value =>
                  rw [indexRun] at run
                  simp only [Prod.mk.injEq] at run
                  obtain ⟨rfl, rfl⟩ := run
                  rfl
              | fn name location selected arity body =>
                rw [evaluate.eq_def] at run
                dsimp only at run
                repeat' split at run
                all_goals simp_all
              | raise trace body =>
                rw [evaluate] at run
                cases bodyRun : evaluate [body] env state with
                | mk bodyResult bodyNext =>
                  rw [bodyRun] at run
                  cases bodyResult with
                  | err error =>
                    simp only [Prod.mk.injEq] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact exprIH [body] env state bodyNext (.err error) (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢
                      omega) bodyRun
                  | val bodyValues =>
                    simp only [Prod.mk.injEq] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact exprIH [body] env state bodyNext (.val bodyValues) (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢
                      omega) bodyRun
              | tick trace body =>
                rw [evaluate] at run
                split at run
                · simp only [timeoutError, Prod.mk.injEq] at run
                  obtain ⟨rfl, rfl⟩ := run
                  rfl
                · exact exprIH [body] env (decClock 1 state) next result (by
                    simp only [decClock]
                    omega) (by
                    simp only [expsWeight, expWeight] at measure ⊢
                    omega) run
              | op trace operation args =>
                have bound := evaluate_clock_le args env state
                rw [evaluate, fixClock_evaluate] at run
                cases argsRun : evaluate args env state with
                | mk argsResult argsNext =>
                  rw [argsRun] at run
                  rw [argsRun] at bound
                  dsimp only at bound
                  cases argsResult with
                  | err error =>
                    simp only [Prod.mk.injEq] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact exprIH args env state argsNext (.err error) (by omega) (by
                      have weighted := opWeight_gt trace operation args
                      simp only [expsWeight] at measure
                      omega) argsRun
                  | val values =>
                    have argsMax : argsNext.maxApp = state.maxApp :=
                      exprIH args env state argsNext (.val values) (by omega) (by
                        have weighted := opWeight_gt trace operation args
                        simp only [expsWeight] at measure
                        omega) argsRun
                    cases operation with
                    | install =>
                      dsimp only at run
                      cases installRun : doInstall values.reverse argsNext with
                      | mk installResult installedState =>
                        rw [installRun] at run
                        cases installResult with
                        | err error =>
                          simp only [Prod.mk.injEq] at run
                          obtain ⟨rfl, rfl⟩ := run
                          exact (doInstall_const values.reverse argsNext (.err error)
                            installedState installRun).1.trans argsMax
                        | val program =>
                          dsimp only at run
                          cases programRun : evaluate program [] installedState with
                          | mk programResult final =>
                            rw [programRun] at run
                            have installedClock := doInstall_success_clock values.reverse
                              argsNext installedState program installRun
                            have installedBefore : installedState.clock < clock := by
                              obtain ⟨positive, decremented⟩ := installedClock
                              omega
                            have installedMax := (doInstall_const values.reverse argsNext
                              (.val program) installedState installRun).1
                            cases programResult with
                            | err error =>
                              simp only [Prod.mk.injEq] at run
                              obtain ⟨rfl, rfl⟩ := run
                              exact ((clockIH installedState.clock installedBefore).2
                                (expsWeight program) program [] installedState final (.err error)
                                rfl rfl programRun).trans (installedMax.trans argsMax)
                            | val programValues =>
                              simp only [Prod.mk.injEq] at run
                              obtain ⟨rfl, rfl⟩ := run
                              exact ((clockIH installedState.clock installedBefore).2
                                (expsWeight program) program [] installedState final
                                (.val programValues) rfl rfl programRun).trans
                                (installedMax.trans argsMax)
                    | thunkOp operation =>
                      cases operation with
                      | forceThunk =>
                        dsimp only at run
                        cases inspected : destThunk values argsNext.refs with
                        | badRef | notThunk =>
                          simp only [inspected, typeError, Prod.mk.injEq] at run
                          obtain ⟨rfl, rfl⟩ := run
                          exact argsMax
                        | isThunk mode value =>
                          cases mode with
                          | evaluated =>
                            simp only [inspected, Prod.mk.injEq] at run
                            obtain ⟨rfl, rfl⟩ := run
                            exact argsMax
                          | notEvaluated =>
                            rw [inspected] at run
                            dsimp only at run
                            cases forceRun : evaluate [appUnit (.var .none 0)] [value] argsNext with
                            | mk forceResult final =>
                              rw [forceRun] at run
                              have forceMax := exprIH [appUnit (.var .none 0)] [value] argsNext
                                final forceResult (by omega) (by
                                have small := appUnit_var_weight
                                simp only [expsWeight, expWeight] at measure small ⊢
                                omega) forceRun
                              cases forceResult with
                              | err error =>
                                simp only [Prod.mk.injEq] at run
                                obtain ⟨rfl, rfl⟩ := run
                                exact forceMax.trans argsMax
                              | val forced =>
                                dsimp only at run
                                cases updated : updateThunk values final.refs forced with
                                | none =>
                                  simp only [updated, typeError, Prod.mk.injEq] at run
                                  obtain ⟨rfl, rfl⟩ := run
                                  exact forceMax.trans argsMax
                                | some refs =>
                                  simp only [updated, Prod.mk.injEq] at run
                                  obtain ⟨rfl, rfl⟩ := run
                                  exact forceMax.trans argsMax
                      | allocThunk mode | updateThunk mode =>
                        dsimp only at run
                        split at run
                        · simp only [Prod.mk.injEq] at run
                          obtain ⟨rfl, rfl⟩ := run
                          exact argsMax
                        · rename_i value last appRun
                          simp only [Prod.mk.injEq] at run
                          obtain ⟨rfl, rfl⟩ := run
                          exact (doApp_maxApp _ values.reverse argsNext
                            last value appRun).trans argsMax
                    | label | ffi | intOp | wordOp | blockOp | globOp | memOp =>
                      dsimp only at run
                      split at run
                      · simp only [Prod.mk.injEq] at run
                        obtain ⟨rfl, rfl⟩ := run
                        exact argsMax
                      · rename_i value last appRun
                        simp only [Prod.mk.injEq] at run
                        obtain ⟨rfl, rfl⟩ := run
                        exact (doApp_maxApp _ values.reverse argsNext last value
                          appRun).trans argsMax
              | «let» trace bindings body =>
                have bound := evaluate_clock_le bindings env state
                rw [evaluate, fixClock_evaluate] at run
                cases bindingRun : evaluate bindings env state with
                | mk bindingResult bindingNext =>
                  simp only [bindingRun] at run bound
                  cases bindingResult with
                  | err error =>
                    simp only [Prod.mk.injEq] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact exprIH bindings env state bindingNext (.err error) (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢
                      omega) bindingRun
                  | val bindingValues =>
                    have bindingMax : bindingNext.maxApp = state.maxApp :=
                      exprIH bindings env state bindingNext (.val bindingValues) (by omega) (by
                        simp only [expsWeight, expWeight] at measure ⊢
                        omega) bindingRun
                    exact (exprIH [body] (bindingValues ++ env) bindingNext next result
                      (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢
                      omega) run).trans bindingMax
              | letrec names location selected functions body =>
                rw [evaluate.eq_def] at run
                dsimp only at run
                split at run
                · split at run
                  · simp only [typeError, Prod.mk.injEq] at run
                    obtain ⟨rfl, rfl⟩ := run
                    rfl
                  · exact exprIH [body] _ state next result (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢
                      omega) run
                · simp only [typeError, Prod.mk.injEq] at run
                  obtain ⟨rfl, rfl⟩ := run
                  rfl
              | ifThenElse trace condition yes no =>
                have bound := evaluate_clock_le [condition] env state
                rw [evaluate, fixClock_evaluate] at run
                cases conditionRun : evaluate [condition] env state with
                | mk conditionResult conditionNext =>
                  simp only [conditionRun] at run bound
                  cases conditionResult with
                  | err error =>
                    simp only [Prod.mk.injEq] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact exprIH [condition] env state conditionNext (.err error) (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢
                      omega) conditionRun
                  | val conditionValues =>
                    have conditionMax : conditionNext.maxApp = state.maxApp :=
                      exprIH [condition] env state conditionNext (.val conditionValues)
                        (by omega) (by
                        simp only [expsWeight, expWeight] at measure ⊢
                        omega) conditionRun
                    dsimp only at run
                    split at run
                    · simp only [typeError, Prod.mk.injEq] at run
                      obtain ⟨rfl, rfl⟩ := run
                      exact conditionMax
                    · exact (exprIH [yes] env conditionNext next result (by omega) (by
                        simp only [expsWeight, expWeight] at measure ⊢
                        omega) run).trans conditionMax
                    · exact (exprIH [no] env conditionNext next result (by omega) (by
                        simp only [expsWeight, expWeight] at measure ⊢
                        omega) run).trans conditionMax
              | handle trace body handler =>
                have bound := evaluate_clock_le [body] env state
                rw [evaluate, fixClock_evaluate] at run
                cases bodyRun : evaluate [body] env state with
                | mk bodyResult bodyNext =>
                  simp only [bodyRun] at run bound
                  cases bodyResult with
                  | val bodyValues =>
                    simp only [Prod.mk.injEq] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact exprIH [body] env state bodyNext (.val bodyValues) (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢
                      omega) bodyRun
                  | err error =>
                    cases error with
                    | abort reason =>
                      simp only [Prod.mk.injEq] at run
                      obtain ⟨rfl, rfl⟩ := run
                      exact exprIH [body] env state bodyNext (.err (.abort reason)) (by omega) (by
                        simp only [expsWeight, expWeight] at measure ⊢
                        omega) bodyRun
                    | raise value =>
                      have bodyMax : bodyNext.maxApp = state.maxApp :=
                        exprIH [body] env state bodyNext (.err (.raise value)) (by omega) (by
                          simp only [expsWeight, expWeight] at measure ⊢
                          omega) bodyRun
                      exact (exprIH [handler] (value :: env) bodyNext next result (by omega) (by
                        simp only [expsWeight, expWeight] at measure ⊢
                        omega) run).trans bodyMax
              | call trace ticks location args =>
                have bound := evaluate_clock_le args env state
                rw [evaluate, fixClock_evaluate] at run
                cases argsRun : evaluate args env state with
                | mk argsResult argsNext =>
                  rw [argsRun] at run
                  rw [argsRun] at bound
                  dsimp only at bound
                  cases argsResult with
                  | err error =>
                    simp only [Prod.mk.injEq] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact exprIH args env state argsNext (.err error) (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢
                      omega) argsRun
                  | val arguments =>
                    have argsMax : argsNext.maxApp = state.maxApp :=
                      exprIH args env state argsNext (.val arguments) (by omega) (by
                        simp only [expsWeight, expWeight] at measure ⊢
                        omega) argsRun
                    dsimp only at run
                    split at run
                    · simp only [typeError, Prod.mk.injEq] at run
                      obtain ⟨rfl, rfl⟩ := run
                      exact argsMax
                    · rename_i selected body found
                      split at run
                      · simp only [timeoutError, Prod.mk.injEq] at run
                        obtain ⟨rfl, rfl⟩ := run
                        exact argsMax
                      · have bodyClock : (decClock (ticks + 1) argsNext).clock < clock := by
                          simp only [decClock]
                          omega
                        exact ((clockIH (decClock (ticks + 1) argsNext).clock bodyClock).2
                          (expsWeight [body]) [body] selected (decClock (ticks + 1) argsNext)
                          next result rfl rfl run).trans argsMax
              | app trace location function args =>
                rw [evaluate] at run
                split at run
                · simp only [typeError, Prod.mk.injEq] at run
                  obtain ⟨rfl, rfl⟩ := run
                  rfl
                · rename_i nonempty
                  cases args with
                  | nil => simp at nonempty
                  | cons first rest =>
                    have argsBound := evaluate_clock_le (first :: rest) env state
                    rw [fixClock_evaluate] at run
                    cases argsRun : evaluate (first :: rest) env state with
                    | mk argsResult argsNext =>
                      simp only [argsRun] at run argsBound
                      cases argsResult with
                      | err error =>
                        simp only [Prod.mk.injEq] at run
                        obtain ⟨rfl, rfl⟩ := run
                        exact exprIH (first :: rest) env state argsNext (.err error) (by omega) (by
                          simp only [expsWeight, expWeight] at measure ⊢
                          omega) argsRun
                      | val arguments =>
                        have argsMax : argsNext.maxApp = state.maxApp :=
                          exprIH (first :: rest) env state argsNext (.val arguments) (by omega) (by
                            simp only [expsWeight, expWeight] at measure ⊢
                            omega) argsRun
                        dsimp only at run
                        rw [fixClock_evaluate] at run
                        have functionBound := evaluate_clock_le [function] env argsNext
                        cases functionRun : evaluate [function] env argsNext with
                        | mk functionResult functionNext =>
                          simp only [functionRun] at run functionBound
                          cases functionResult with
                          | err error =>
                            simp only [Prod.mk.injEq] at run
                            obtain ⟨rfl, rfl⟩ := run
                            exact (exprIH [function] env argsNext functionNext (.err error)
                              (by omega) (by
                              simp only [expsWeight, expWeight] at measure ⊢
                              omega) functionRun).trans argsMax
                          | val functionValues =>
                            have functionMax : functionNext.maxApp = argsNext.maxApp :=
                              exprIH [function] env argsNext functionNext (.val functionValues)
                                (by omega) (by
                                simp only [expsWeight, expWeight] at measure ⊢
                                omega) functionRun
                            change ClosSem.evaluateApp location
                              (@Flapjack.holHd ClosSem.Value ⟨ClosSem.unitValue⟩ functionValues)
                              arguments functionNext = (result, next) at run
                            exact (appIH location _ arguments functionNext next result
                              (by omega) run).trans (functionMax.trans argsMax)
  constructor
  · intro expressions env state next result run
    exact (all state.clock).2 (expsWeight expressions) expressions env state next result rfl rfl run
  · intro location function args state next result run
    exact (all state.clock).1 location function args state next result rfl run

/-- Evaluation preserves the maximum application arity. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_const"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateConst {C F : Type} (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
    (state : State C F) (result : Result (List ClosSem.Value) ClosSem.Value) (next : State C F)
    (run : evaluate expressions env state = (result, next)) : next.maxApp = state.maxApp :=
  evaluateConst_both.1 expressions env state next result run

/-- Application preserves the maximum application arity. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_app_const"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAppConst {C F : Type} (location : Option Nat) (function : ClosSem.Value)
    (args : List ClosSem.Value) (state : State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value) (next : State C F)
    (run : evaluateApp location function args state = (result, next)) :
    next.maxApp = state.maxApp :=
  evaluateConst_both.2 location function args state next result run

end Flapjack.Compiler.Backend.ClosProps
