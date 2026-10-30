import Flapjack.Compiler.Backend.ClosInterp.Proofs.InstallRelation

/-! Closure application simulation for the proof-side evaluator. The evaluator
and state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- Subtracting the same amount from related clocks preserves the relation. -/
theorem stateRel_decClock {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel source target) (amount : Nat) :
    StateRel (ClosSem.decClock amount source) (ClosSem.decClock amount target) := by
  have clockEq : target.clock = source.clock := related.1.2.2.2.2.2.1
  have h := stateRel_withClock related (source.clock - amount)
  simpa [ClosSem.decClock, clockEq] using h

/-- A full closure application evaluates its body before remaining arguments. -/
theorem evaluateApp_full_step {C F : Type} (location : Option Nat) (function : ClosSem.Value)
    (first : ClosSem.Value) (rest : List ClosSem.Value) (state : ClosSem.State C F)
    (body : ClosLang.Exp) (bodyEnv remaining : List ClosSem.Value)
    (found : ClosSem.destClosure state.maxApp location function (first :: rest) =
      some (.fullApp body bodyEnv remaining))
    (enough : (first :: rest).length - remaining.length ≤ state.clock) :
    ClosSem.evaluateApp location function (first :: rest) state =
      match ClosSem.evaluate [body] bodyEnv (ClosSem.decClock ((first :: rest).length - remaining.length) state) with
      | (.val [value], next) => ClosSem.evaluateApp location value remaining next
      | (other, next) => (other, next) := by
  rw [ClosSem.evaluateApp, found]
  simp only [not_lt.mpr enough, ↓reduceIte, ClosSem.fixClock_evaluate]
  cases run : ClosSem.evaluate [body] bodyEnv (ClosSem.decClock ((first :: rest).length - remaining.length) state) with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values =>
      cases values with
      | nil => rfl
      | cons first tail => cases tail <;> rfl

/-- Closure application simulation from smaller-clock body and application
induction hypotheses. -/
theorem evaluateApp_simulation_step {C F : Type} (location : Option Nat) (function : ClosSem.Value)
    (args : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyIH : ∀ (body : ClosLang.Exp) (env : List ClosSem.Value) (bodySource bodyTarget bodyFinal : ClosSem.State C F)
      (bodyResult : Result (List ClosSem.Value) ClosSem.Value),
      bodySource.clock < source.clock → ClosSem.evaluate [body] env bodySource = (bodyResult, bodyFinal) →
      StateRel bodySource bodyTarget → bodyResult ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [body] env { bodyTarget with clock := extra + bodyTarget.clock } = (bodyResult, targetFinal) ∧
        StateRel bodyFinal targetFinal)
    (appIH : ∀ (value : ClosSem.Value) (rest : List ClosSem.Value) (appSource appTarget appFinal : ClosSem.State C F)
      (appResult : Result (List ClosSem.Value) ClosSem.Value),
      appSource.clock < source.clock → ClosSem.evaluateApp location value rest appSource = (appResult, appFinal) →
      StateRel appSource appTarget → appResult ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluateApp location value rest { appTarget with clock := extra + appTarget.clock } = (appResult, targetFinal) ∧
        StateRel appFinal targetFinal)
    (related : StateRel source target)
    (run : ClosSem.evaluateApp location function args source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluateApp location function args { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  have maxEq : target.maxApp = source.maxApp := related.1.2.2.2.1
  have clockEq : target.clock = source.clock := related.1.2.2.2.2.2.1
  cases args with
  | nil =>
    simp [ClosSem.evaluateApp] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨0, target, ?_, related⟩
    simp [ClosSem.evaluateApp]
  | cons first rest =>
    cases found : ClosSem.destClosure source.maxApp location function (first :: rest) with
    | none =>
      rw [ClosSem.evaluateApp, found] at run
      simp at run
      exact (notTypeError run.1.symm).elim
    | some kind =>
      have foundTarget : ClosSem.destClosure target.maxApp location function (first :: rest) = some kind := by
        simpa [maxEq] using found
      cases kind with
      | partialApp value =>
        rw [ClosSem.evaluateApp, found] at run
        dsimp only at run
        by_cases timeout : source.clock < (first :: rest).length
        · rw [if_pos timeout] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨0, { target with clock := 0 }, ?_, ?_⟩
          · simp only [Nat.zero_add]
            change ClosSem.evaluateApp location function (first :: rest) target = _
            rw [ClosSem.evaluateApp, foundTarget]
            dsimp only
            rw [if_pos (by simpa [clockEq] using timeout)]
            rfl
          · exact stateRel_withClock related 0
        · rw [if_neg timeout] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨0, ClosSem.decClock (first :: rest).length target, ?_, stateRel_decClock source target related _⟩
          simp only [Nat.zero_add]
          change ClosSem.evaluateApp location function (first :: rest) target = _
          rw [ClosSem.evaluateApp, foundTarget]
          dsimp only
          rw [if_neg (by simpa [clockEq] using timeout)]
      | fullApp body bodyEnv remaining =>
        have remainingLt := ClosSem.destClosure_full_remaining_lt source.maxApp location function (first :: rest)
          bodyEnv remaining body found
        let cost := (first :: rest).length - remaining.length
        have positive : 0 < cost := Nat.sub_pos_of_lt remainingLt
        by_cases timeout : source.clock < cost
        · rw [ClosSem.evaluateApp, found] at run
          dsimp only at run
          rw [if_pos timeout] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨0, { target with clock := 0 }, ?_, ?_⟩
          · simp only [Nat.zero_add]
            change ClosSem.evaluateApp location function (first :: rest) target = _
            rw [ClosSem.evaluateApp, foundTarget]
            dsimp only
            rw [if_pos (by simpa [clockEq, cost] using timeout)]
            rfl
          · exact stateRel_withClock related 0
        · have enough : cost ≤ source.clock := by omega
          have smaller : (ClosSem.decClock cost source).clock < source.clock := by simp [ClosSem.decClock]; omega
          have bodyRelated := stateRel_decClock source target related cost
          have targetStep (extra : Nat) :
              ClosSem.evaluateApp location function (first :: rest) { target with clock := extra + target.clock } =
                match ClosSem.evaluate [body] bodyEnv
                  { ClosSem.decClock cost target with clock := extra + (ClosSem.decClock cost target).clock } with
                | (.val [value], next) => ClosSem.evaluateApp location value remaining next
                | (other, next) => (other, next) := by
            have found' : ClosSem.destClosure { target with clock := extra + target.clock }.maxApp location function (first :: rest) =
                some (.fullApp body bodyEnv remaining) := by simpa using foundTarget
            have enough' : (first :: rest).length - remaining.length ≤ ({ target with clock := extra + target.clock } : ClosSem.State C F).clock := by
              simp only [cost] at enough
              simp only
              omega
            rw [evaluateApp_full_step location function first rest _ body bodyEnv remaining found' enough']
            have clocks : ClosSem.decClock cost { target with clock := extra + target.clock } =
                { ClosSem.decClock cost target with clock := extra + (ClosSem.decClock cost target).clock } := by
              simp only [ClosSem.decClock]
              congr 1
              omega
            rw [show (first :: rest).length - remaining.length = cost from rfl, clocks]
          rw [evaluateApp_full_step location function first rest source body bodyEnv remaining found (by simpa [cost] using enough)] at run
          cases bodyRun : ClosSem.evaluate [body] bodyEnv (ClosSem.decClock cost source) with
          | mk bodyResult sourceMid =>
            have bodyBound : sourceMid.clock ≤ (ClosSem.decClock cost source).clock := by
              have h := ClosSem.evaluate_clock_le [body] bodyEnv (ClosSem.decClock cost source)
              simpa [bodyRun] using h
            rw [bodyRun] at run
            have bodyNotTypeError : bodyResult ≠ .err (.abort .typeError) := by
              intro bad
              subst bodyResult
              simp at run
              exact notTypeError run.1.symm
            obtain ⟨bodyExtra, targetMid, targetBody, midRel⟩ :=
              bodyIH body bodyEnv (ClosSem.decClock cost source) (ClosSem.decClock cost target) sourceMid
                bodyResult smaller bodyRun bodyRelated bodyNotTypeError
            cases bodyResult with
            | err error =>
              simp at run
              rcases run with ⟨rfl, rfl⟩
              refine ⟨bodyExtra, targetMid, ?_, midRel⟩
              rw [targetStep, targetBody]
            | val bodyValues =>
              obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value body bodyEnv
                (ClosSem.decClock cost source) sourceMid bodyValues bodyRun
              dsimp only at run
              obtain ⟨appExtra, targetFinal, targetApp, finalRel⟩ :=
                appIH value remaining sourceMid targetMid sourceFinal result (by omega) run midRel notTypeError
              have shiftedBody := ClosSem.evaluate_addClock.1 [body] bodyEnv
                { ClosSem.decClock cost target with clock := bodyExtra + (ClosSem.decClock cost target).clock }
                targetMid (.val [value]) appExtra targetBody (by simp)
              have bodyRun' : ClosSem.evaluate [body] bodyEnv
                  { ClosSem.decClock cost target with clock := (bodyExtra + appExtra) + (ClosSem.decClock cost target).clock } =
                  (.val [value], { targetMid with clock := appExtra + targetMid.clock }) := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using shiftedBody
              refine ⟨bodyExtra + appExtra, targetFinal, ?_, finalRel⟩
              rw [targetStep, bodyRun']
              exact targetApp

/-- Application-expression simulation from argument, function, and closure
application induction hypotheses. -/
theorem evaluate_app_simulation_step {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsIH : ∀ (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env source = (result, sourceFinal) → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal, ClosSem.evaluate args env { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (functionIH : ∀ (fnSource fnTarget fnFinal : ClosSem.State C F) (fnResult : Result (List ClosSem.Value) ClosSem.Value),
      fnSource.clock ≤ source.clock → ClosSem.evaluate [function] env fnSource = (fnResult, fnFinal) →
      StateRel fnSource fnTarget → fnResult ≠ .err (.abort .typeError) →
      ∃ extra targetFinal, ClosSem.evaluate [function] env { fnTarget with clock := extra + fnTarget.clock } = (fnResult, targetFinal) ∧
        StateRel fnFinal targetFinal)
    (appIH : ∀ (fn : ClosSem.Value) (values : List ClosSem.Value) (appSource appTarget appFinal : ClosSem.State C F)
      (appResult : Result (List ClosSem.Value) ClosSem.Value),
      appSource.clock ≤ source.clock → ClosSem.evaluateApp location fn values appSource = (appResult, appFinal) →
      StateRel appSource appTarget → appResult ≠ .err (.abort .typeError) →
      ∃ extra targetFinal, ClosSem.evaluateApp location fn values { appTarget with clock := extra + appTarget.clock } =
        (appResult, targetFinal) ∧ StateRel appFinal targetFinal)
    (related : StateRel source target)
    (run : ClosSem.evaluate [.app trace location function args] env source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [.app trace location function args] env { target with clock := extra + target.clock } =
        (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  cases args with
  | nil =>
    simp [ClosSem.evaluate] at run
    exact (notTypeError run.1.symm).elim
  | cons first rest =>
    cases argsRun : ClosSem.evaluate (first :: rest) env source with
    | mk argsResult sourceMid =>
      have bound : sourceMid.clock ≤ source.clock := by
        have h := ClosSem.evaluate_clock_le (first :: rest) env source
        simpa [argsRun] using h
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, argsRun] at run
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
      have argsNotTypeError : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        simp at run
        exact notTypeError run.1.symm
      obtain ⟨argsExtra, targetMid, targetArgs, midRel⟩ := argsIH source target sourceMid argsResult argsRun related argsNotTypeError
      cases argsResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨argsExtra, targetMid, ?_, midRel⟩
        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs]
        simp
      | val values =>
        dsimp only at run
        rw [ClosSem.fixClock_evaluate] at run
        cases functionRun : ClosSem.evaluate [function] env sourceMid with
        | mk fnResult sourceReady =>
          have fnBound : sourceReady.clock ≤ source.clock := by
            have h := ClosSem.evaluate_clock_le [function] env sourceMid
            simp only [functionRun] at h
            omega
          rw [functionRun] at run
          have fnNotTypeError : fnResult ≠ .err (.abort .typeError) := by
            intro bad
            subst fnResult
            simp at run
            exact notTypeError run.1.symm
          obtain ⟨fnExtra, targetReady, targetFn, readyRel⟩ :=
            functionIH sourceMid targetMid sourceReady fnResult bound functionRun midRel fnNotTypeError
          cases fnResult with
          | err error =>
            simp at run
            rcases run with ⟨rfl, rfl⟩
            have shiftedArgs := ClosSem.evaluate_addClock.1 (first :: rest) env
              { target with clock := argsExtra + target.clock } targetMid (.val values) fnExtra targetArgs (by simp)
            let enlarged := { target with clock := (argsExtra + target.clock) + fnExtra }
            let enlargedMid := { targetMid with clock := targetMid.clock + fnExtra }
            have targetArgs' : ClosSem.evaluate (first :: rest) env enlarged = (.val values, enlargedMid) := by
              simpa [enlarged, enlargedMid] using shiftedArgs
            have targetFn' : ClosSem.evaluate [function] env enlargedMid = (.err error, targetReady) := by
              simpa [enlargedMid, Nat.add_comm] using targetFn
            refine ⟨argsExtra + fnExtra, targetReady, ?_, readyRel⟩
            have targetRun : ClosSem.evaluate [.app trace location function (first :: rest)] env enlarged =
                (.err error, targetReady) := by
              rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs']
              simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
              rw [ClosSem.fixClock_evaluate, targetFn']
            simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetRun
          | val functionValues =>
            obtain ⟨fn, rfl⟩ := ClosSem.evaluate_singleton_value function env sourceMid sourceReady functionValues functionRun
            change ClosSem.evaluateApp location fn values sourceReady = (result, sourceFinal) at run
            obtain ⟨appExtra, targetFinal, targetApp, finalRel⟩ :=
              appIH fn values sourceReady targetReady sourceFinal result fnBound run readyRel notTypeError
            let argsOffset := fnExtra + appExtra
            let enlarged := { target with clock := (argsExtra + target.clock) + argsOffset }
            let enlargedMid := { targetMid with clock := targetMid.clock + argsOffset }
            let enlargedReady := { targetReady with clock := targetReady.clock + appExtra }
            have shiftedArgs := ClosSem.evaluate_addClock.1 (first :: rest) env
              { target with clock := argsExtra + target.clock } targetMid (.val values) argsOffset targetArgs (by simp)
            have shiftedFn := ClosSem.evaluate_addClock.1 [function] env
              { targetMid with clock := fnExtra + targetMid.clock } targetReady (.val [fn]) appExtra targetFn (by simp)
            have targetArgs' : ClosSem.evaluate (first :: rest) env enlarged = (.val values, enlargedMid) := by
              simpa [enlarged, enlargedMid] using shiftedArgs
            have targetFn' : ClosSem.evaluate [function] env enlargedMid = (.val [fn], enlargedReady) := by
              simpa [enlargedMid, enlargedReady, argsOffset, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using shiftedFn
            have targetApp' : ClosSem.evaluateApp location fn values enlargedReady = (result, targetFinal) := by
              simpa [enlargedReady, Nat.add_comm] using targetApp
            refine ⟨argsExtra + argsOffset, targetFinal, ?_, finalRel⟩
            have targetRun : ClosSem.evaluate [.app trace location function (first :: rest)] env enlarged = (result, targetFinal) := by
              rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs']
              simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
              rw [ClosSem.fixClock_evaluate, targetFn']
              exact targetApp'
            simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetRun

end Flapjack.Compiler.Backend.ClosInterp
