import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.ApplicationExpression

/-! Direct-code-call simulation for closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A direct call uses related code entries and arguments; its body is an
induction case at a smaller clock. -/
theorem evaluate_call_step {C F : Type} (trace : BackendCommon.Tra) (ticks location : Nat)
    (args : List ClosLang.Exp) (source : State C F) (argsIH : EvalSimulationAt source args)
    (bodyIH : ∀ (body : ClosLang.Exp) (state : State C F), state.clock < source.clock →
      EvalSimulationAt state [body]) :
    EvalSimulationAt source [.call trace ticks location args] := by
  intro env nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have argsVars : ∀ n, altFv n args = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    simpa [altFv_call] using present
  have argsSafe : everyFnVarsNone args := by simpa [everyFnVarsNone, fnVarsNoneExp] using safe
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, argsRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv target (.err error) middle m l index argsRun noType length argsVars
          argsSafe code oracle states
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        rw [altFree_call]
        simp only [shiftList, shiftSing]
        rw [evaluate, fixClock_evaluate, targetRun]
    | val values =>
      have valuesNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv target (.val values) middle m l index argsRun valuesNoType length argsVars
          argsSafe code oracle states
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at resultRel
      | val nextValues =>
        have middleSafe := (evaluate_preserves_safe.1 args) env source (.val values) middle argsRun code oracle
        have middleClock : middle.clock ≤ source.clock := by
          have h := evaluate_clock_le args env source
          simpa [argsRun] using h
        have codeRel := middleRel.2.2.2.2.2.2.2 location
        cases found : middle.code.lookup location with
        | none =>
          rw [evaluate, fixClock_evaluate, argsRun] at run
          simp [findCode, found] at run
          exact False.elim (noType run.1.symm)
        | some entry =>
          obtain ⟨arity, body⟩ := entry
          cases nextFound : targetMiddle.code.lookup location with
          | none => simp [found, nextFound, optionRel] at codeRel
          | some nextEntry =>
            have entryRel : CodeRel (arity, body) nextEntry := by simpa [found, nextFound, optionRel] using codeRel
            have nextEntryEq : nextEntry = (arity, annotateSing arity body) := entryRel
            subst nextEntry
            by_cases arityEq : values.length = arity
            · have nextArityEq : nextValues.length = arity := by rw [← resultRel.length_eq]; exact arityEq
              have sourceFind : findCode location values middle.code = some (values, body) := by
                simp [findCode, found, arityEq]
              have targetFind : findCode location nextValues targetMiddle.code =
                  some (nextValues, annotateSing arity body) := by simp [findCode, nextFound, nextArityEq]
              rw [evaluate, fixClock_evaluate, argsRun] at run
              dsimp only at run
              rw [sourceFind] at run
              dsimp only at run
              by_cases timeout : middle.clock < ticks + 1
              · have targetTimeout : targetMiddle.clock < ticks + 1 := by simpa [← middleRel.1] using timeout
                rw [if_pos timeout] at run
                cases run
                refine ⟨.err (.abort .timeoutError), { targetMiddle with clock := 0 }, ?_, rfl,
                  stateRel_withClock middleRel 0⟩
                rw [altFree_call]
                simp only [shiftList, shiftSing]
                rw [evaluate, fixClock_evaluate, targetRun]
                dsimp only
                rw [targetFind]
                dsimp only
                rw [if_pos targetTimeout]
                rfl
              · have targetEnough : ¬ targetMiddle.clock < ticks + 1 := by simpa [← middleRel.1] using timeout
                have startRel : StateRel (decClock (ticks + 1) middle) (decClock (ticks + 1) targetMiddle) := by
                  simpa [decClock, ← middleRel.1] using stateRel_withClock middleRel (middle.clock - (ticks + 1))
                have smaller : (decClock (ticks + 1) middle).clock < source.clock := by
                  simp [decClock]
                  omega
                have bodySafe : everyFnVarsNone [body] := middleSafe.1 location arity body found
                have bodyVars : ∀ n, altFv n [body] = true → EnvOk 0 arity .ln values nextValues n := by
                  have h := envOk_application_body body 0 arity .ln [] [] values nextValues resultRel arityEq (by
                    intro n present bound
                    exact .outside 0 0 .ln [] [] (n - arity) (by omega))
                  simpa using h
                rw [if_neg timeout] at run
                obtain ⟨targetBodyResult, targetLast, targetBodyRun, bodyRel, lastRel⟩ :=
                  bodyIH body (decClock (ticks + 1) middle) smaller values nextValues
                    (decClock (ticks + 1) targetMiddle) result sourceNext 0 arity .ln run noType (by simpa using arityEq)
                    bodyVars bodySafe (by simpa [CodeSafe, decClock] using middleSafe.1)
                    (by simpa [OracleSafe, decClock] using middleSafe.2) startRel
                refine ⟨targetBodyResult, targetLast, ?_, bodyRel, lastRel⟩
                rw [altFree_call]
                simp only [shiftList, shiftSing]
                rw [evaluate, fixClock_evaluate, targetRun]
                dsimp only
                rw [targetFind]
                dsimp only
                rw [if_neg targetEnough]
                simpa [annotateSing, altFree_singleton, shiftList] using targetBodyRun
            · rw [evaluate, fixClock_evaluate, argsRun] at run
              simp [findCode, found, arityEq] at run
              exact False.elim (noType run.1.symm)

end Flapjack.Compiler.Backend.ClosAnnotate
