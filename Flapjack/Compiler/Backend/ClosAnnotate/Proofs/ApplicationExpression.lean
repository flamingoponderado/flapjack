module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.ClosureApplication

@[expose] public section

/-! Application-expression simulation for closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- An application expression composes its argument and function simulations
with closure application at a reachable clock. -/
theorem evaluate_app_step {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (source : State C F)
    (argsIH : EvalSimulationAt source args)
    (functionIH : ∀ state : State C F, state.clock ≤ source.clock → EvalSimulationAt state [function])
    (applicationIH : AppSimulationClockBelow (C := C) (F := F) (source.clock + 1)) :
    EvalSimulationAt source [.app trace location function args] := by
  intro env nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have functionVars : ∀ n, altFv n [function] = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    rw [altFv_app]
    simp [present]
  have argsVars : ∀ n, altFv n args = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    rw [altFv_app]
    simp [present]
  have safeParts : everyFnVarsNone [function] ∧ everyFnVarsNone args := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using safe
  cases args with
  | nil =>
    simp [evaluate] at run
    exact False.elim (noType run.1.symm)
  | cons first rest =>
    cases argsRun : evaluate (first :: rest) env source with
    | mk argsResult middle =>
      have middleClock : middle.clock ≤ source.clock := by
        have h := evaluate_clock_le (first :: rest) env source
        simpa [argsRun] using h
      have middleSafe := (evaluate_preserves_safe.1 (first :: rest)) env source argsResult middle argsRun code oracle
      cases argsResult with
      | err error =>
        rw [evaluate, fixClock_evaluate, argsRun] at run
        cases run
        obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
          argsIH env nextEnv target (.err error) middle m l index argsRun noType length argsVars
            safeParts.2 code oracle states
        cases targetResult with
        | val values => cases error <;> simp [ResultRel] at resultRel
        | err targetError =>
          refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
          rw [altFree_app]
          simp only [altFree_singleton, shiftList, shiftSing, Flapjack.holHd]
          simp only [altFree, altFreeList, shiftList] at targetRun ⊢
          rw [evaluate, fixClock_evaluate, targetRun]
          rfl
      | val values =>
        have argsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
        obtain ⟨targetArgsResult, targetMiddle, targetArgsRun, argsRel, middleRel⟩ :=
          argsIH env nextEnv target (.val values) middle m l index argsRun argsNoType length argsVars
            safeParts.2 code oracle states
        cases targetArgsResult with
        | err error => cases error <;> simp [ResultRel] at argsRel
        | val targetValues =>
          cases functionRun : evaluate [function] env middle with
          | mk functionResult last =>
            have lastSafe := (evaluate_preserves_safe.1 [function]) env middle functionResult last functionRun
              middleSafe.1 middleSafe.2
            cases functionResult with
            | err error =>
              rw [evaluate, fixClock_evaluate, argsRun] at run
              simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
              rw [fixClock_evaluate, functionRun] at run
              cases run
              obtain ⟨targetResult, targetLast, targetRun, resultRel, lastRel⟩ :=
                functionIH middle middleClock env nextEnv targetMiddle (.err error) last m l index functionRun
                  noType length functionVars safeParts.1 middleSafe.1 middleSafe.2 middleRel
              cases targetResult with
              | val values => cases error <;> simp [ResultRel] at resultRel
              | err targetError =>
                refine ⟨.err targetError, targetLast, ?_, resultRel, lastRel⟩
                rw [altFree_app]
                simp only [altFree_singleton, shiftList, shiftSing, Flapjack.holHd] at targetRun ⊢
                simp only [altFree, altFreeList, shiftList] at targetArgsRun ⊢
                rw [evaluate, fixClock_evaluate, targetArgsRun]
                simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
                rw [fixClock_evaluate, targetRun]
            | val functions =>
              have size := (evaluate_length (C := C) (F := F)).1 [function] env middle last functions functionRun
              cases functions with
              | nil => simp at size
              | cons value tail =>
                cases tail with
                | cons value' tail => simp at size
                | nil =>
                  have functionNoType : (Result.val [value] : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
                  obtain ⟨targetFunctionResult, targetLast, targetFunctionRun, functionRel, lastRel⟩ :=
                    functionIH middle middleClock env nextEnv targetMiddle (.val [value]) last m l index functionRun
                      functionNoType length functionVars safeParts.1 middleSafe.1 middleSafe.2 middleRel
                  cases targetFunctionResult with
                  | err error => cases error <;> simp [ResultRel] at functionRel
                  | val targetFunctions =>
                    cases functionRel with
                    | cons valueRel tailRel =>
                      cases tailRel
                      rename_i targetValue
                      have appRun : evaluateApp location value values last = (result, sourceNext) := by
                        rw [evaluate, fixClock_evaluate, argsRun] at run
                        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
                        rw [fixClock_evaluate, functionRun] at run
                        simpa using run
                      have lastClock : last.clock ≤ source.clock := by
                        have h := evaluate_clock_le [function] env middle
                        rw [functionRun] at h
                        simp only at h
                        omega
                      obtain ⟨targetResult, targetNext, targetAppRun, resultRel, nextRel⟩ :=
                        applicationIH location value targetValue values targetValues last targetLast result sourceNext
                          (by omega) appRun noType valueRel argsRel lastSafe.1 lastSafe.2 lastRel
                      refine ⟨targetResult, targetNext, ?_, resultRel, nextRel⟩
                      rw [altFree_app]
                      simp only [altFree_singleton, shiftList, shiftSing, Flapjack.holHd] at targetFunctionRun ⊢
                      simp only [altFree, altFreeList, shiftList] at targetArgsRun ⊢
                      rw [evaluate, fixClock_evaluate, targetArgsRun]
                      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
                      rw [fixClock_evaluate, targetFunctionRun]
                      simpa using targetAppRun

end Flapjack.Compiler.Backend.ClosAnnotate
