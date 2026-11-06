import Flapjack.Compiler.Backend.Semantics.ClosSem.Semantics
import Flapjack.Compiler.Backend.Semantics.ClosSem.AppClockShift

/-! Clocked simulation consequences for the proof-side observational semantics.
The evaluator and state carriers await HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- A non-timeout initial evaluation is unchanged by additional clock, apart
from the final clock field. -/
theorem evaluate_initial_addClock {C F : Type} (ffi : HolFfiState F) (maxApp clock extra : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (program : List ClosLang.Exp) (result : Result (List Value) Value)
    (final : State C F) (run : evaluate program [] (initialState ffi maxApp code oracle compiler clock) = (result, final))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate program [] (initialState ffi maxApp code oracle compiler (clock + extra)) =
      (result, { final with clock := final.clock + extra }) := by
  have shifted := evaluate_addClock.1 program [] (initialState ffi maxApp code oracle compiler clock)
    final result extra run notTimeout
  simpa [initialState] using shifted

/-- A forward clocked simulation from a non-failing source rules out target
type errors. -/
theorem simulation_target_noTypeError {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (sourceOracle targetOracle : CompileOracle C)
    (sourceCompiler targetCompiler : Compiler C) (program : List ClosLang.Exp)
    (sourceSafe : ∀ clock, (evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler clock)).1 ≠ .err (.abort .typeError))
    (simulation : ∀ clock result final,
      evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler clock) = (result, final) →
      ∃ extra targetFinal, evaluate program [] (initialState ffi maxApp code targetOracle targetCompiler (clock + extra)) =
        (result, targetFinal) ∧ final.ffi = targetFinal.ffi) :
    ∀ clock, (evaluate program [] (initialState ffi maxApp code targetOracle targetCompiler clock)).1 ≠ .err (.abort .typeError) := by
  intro clock targetError
  cases sourceRun : evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler clock) with
  | mk sourceResult sourceFinal =>
    obtain ⟨extra, targetFinal, targetRun, _⟩ := simulation clock sourceResult sourceFinal sourceRun
    cases targetRun0 : evaluate program [] (initialState ffi maxApp code targetOracle targetCompiler clock) with
    | mk targetResult targetFinal0 =>
      have targetResultEq : targetResult = .err (.abort .typeError) := by simpa [targetRun0] using targetError
      subst targetResult
      have shifted := evaluate_initial_addClock ffi maxApp clock extra code targetOracle targetCompiler program
        (.err (.abort .typeError)) targetFinal0 targetRun0 (by simp)
      rw [targetRun] at shifted
      have sourceError : sourceResult = .err (.abort .typeError) := (Prod.mk.inj shifted).1
      exact sourceSafe clock (by simpa [sourceRun] using sourceError)

/-- A forward clocked simulation preserves all terminating observations in
both directions, because a terminating target run remains stable at the
simulated clock. -/
theorem simulation_terminatingObservation_eq {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (sourceOracle targetOracle : CompileOracle C)
    (sourceCompiler targetCompiler : Compiler C) (program : List ClosLang.Exp)
    (simulation : ∀ clock result final,
      evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler clock) = (result, final) →
      ∃ extra targetFinal, evaluate program [] (initialState ffi maxApp code targetOracle targetCompiler (clock + extra)) =
        (result, targetFinal) ∧ final.ffi = targetFinal.ffi) :
    terminatingObservation ffi maxApp code sourceOracle sourceCompiler program =
      terminatingObservation ffi maxApp code targetOracle targetCompiler program := by
  funext behavior
  apply propext
  constructor
  · rintro ⟨clock, result, final, outcome, run, outcomeEq, behaviorEq⟩
    obtain ⟨extra, targetFinal, targetRun, ffiEq⟩ := simulation clock result final run
    exact ⟨clock + extra, result, targetFinal, outcome, targetRun, outcomeEq, by simpa [ffiEq] using behaviorEq⟩
  · rintro ⟨clock, result, targetFinal, outcome, targetRun, outcomeEq, behaviorEq⟩
    have notTimeout : result ≠ .err (.abort .timeoutError) := by
      intro impossible
      subst result
      simp at outcomeEq
    cases sourceRun : evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler clock) with
    | mk sourceResult sourceFinal =>
      obtain ⟨extra, simulatedFinal, simulatedRun, ffiEq⟩ := simulation clock sourceResult sourceFinal sourceRun
      have shifted := evaluate_initial_addClock ffi maxApp clock extra code targetOracle targetCompiler program
        result targetFinal targetRun notTimeout
      rw [simulatedRun] at shifted
      obtain ⟨resultEq, stateEq⟩ := Prod.mk.inj shifted
      subst sourceResult
      have finalFfi : sourceFinal.ffi = targetFinal.ffi := by
        rw [ffiEq, stateEq]
      exact ⟨clock, result, sourceFinal, outcome, sourceRun, outcomeEq, by simpa [finalFfi] using behaviorEq⟩

/-- Monotone clock-indexed traces with a forward clock-extension simulation
have the same lazy-list limit. -/
theorem clocked_traces_lub_eq {α : Type} (source target : Nat → List α)
    (sourceMono : ∀ k l, k ≤ l → source k <+: source l)
    (targetMono : ∀ k l, k ≤ l → target k <+: target l)
    (simulation : ∀ clock, ∃ extra, source clock = target (clock + extra)) :
    HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList (source clock)) =
      HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList (target clock)) := by
  apply HolLList.IMP_build_lprefix_lub_EQ
  · intro x y ⟨k, hk⟩ ⟨l, hl⟩
    subst x; subst y
    rcases Nat.le_total k l with h | h
    · exact Or.inl ((HolLList.lprefix_fromList _ _).2 (sourceMono k l h))
    · exact Or.inr ((HolLList.lprefix_fromList _ _).2 (sourceMono l k h))
  · intro x y ⟨k, hk⟩ ⟨l, hl⟩
    subst x; subst y
    rcases Nat.le_total k l with h | h
    · exact Or.inl ((HolLList.lprefix_fromList _ _).2 (targetMono k l h))
    · exact Or.inr ((HolLList.lprefix_fromList _ _).2 (targetMono l k h))
  · intro trace ⟨clock, h⟩
    subst trace
    obtain ⟨extra, equal⟩ := simulation clock
    refine ⟨HolLList.fromList (target (clock + extra)), ⟨clock + extra, rfl⟩, ?_⟩
    apply (HolLList.lprefix_fromList _ _).2
    rw [equal]
    exact List.prefix_refl _
  · intro trace ⟨clock, h⟩
    subst trace
    obtain ⟨extra, equal⟩ := simulation clock
    refine ⟨HolLList.fromList (source clock), ⟨clock, rfl⟩, ?_⟩
    apply (HolLList.lprefix_fromList _ _).2
    rw [equal]
    exact targetMono clock (clock + extra) (Nat.le_add_right clock extra)

/-- A forward clock-extension simulation preserves proof-side observations
when both evaluators' event traces are monotone in the initial clock. -/
theorem semantics_eq_of_clocked_simulation {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (sourceOracle targetOracle : CompileOracle C)
    (sourceCompiler targetCompiler : Compiler C) (program : List ClosLang.Exp)
    (sourceSafe : ∀ clock, (evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler clock)).1 ≠ .err (.abort .typeError))
    (simulation : ∀ clock result final,
      evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler clock) = (result, final) →
      ∃ extra targetFinal, evaluate program [] (initialState ffi maxApp code targetOracle targetCompiler (clock + extra)) =
        (result, targetFinal) ∧ final.ffi = targetFinal.ffi)
    (sourceMono : ∀ k l, k ≤ l →
      (evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler k)).2.ffi.ioEvents <+:
        (evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler l)).2.ffi.ioEvents)
    (targetMono : ∀ k l, k ≤ l →
      (evaluate program [] (initialState ffi maxApp code targetOracle targetCompiler k)).2.ffi.ioEvents <+:
        (evaluate program [] (initialState ffi maxApp code targetOracle targetCompiler l)).2.ffi.ioEvents) :
    semantics ffi maxApp code sourceOracle sourceCompiler program = semantics ffi maxApp code targetOracle targetCompiler program := by
  classical
  have targetSafe := simulation_target_noTypeError ffi maxApp code sourceOracle targetOracle sourceCompiler targetCompiler program sourceSafe simulation
  have terminatingEq := simulation_terminatingObservation_eq ffi maxApp code sourceOracle targetOracle sourceCompiler targetCompiler program simulation
  have tracesEq :
      HolLList.buildLprefixLub (fun trace => ∃ clock,
        trace = HolLList.fromList (evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler clock)).2.ffi.ioEvents) =
      HolLList.buildLprefixLub (fun trace => ∃ clock,
        trace = HolLList.fromList (evaluate program [] (initialState ffi maxApp code targetOracle targetCompiler clock)).2.ffi.ioEvents) := by
    apply clocked_traces_lub_eq _ _ sourceMono targetMono
    intro clock
    cases sourceRun : evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler clock) with
    | mk result final =>
      obtain ⟨extra, targetFinal, targetRun, ffiEq⟩ := simulation clock result final sourceRun
      exact ⟨extra, by simp [targetRun, ffiEq]⟩
  unfold semantics
  simp only [show ¬ ∃ clock, (evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler clock)).1 = .err (.abort .typeError) from
    fun ⟨clock, error⟩ => sourceSafe clock error,
    show ¬ ∃ clock, (evaluate program [] (initialState ffi maxApp code targetOracle targetCompiler clock)).1 = .err (.abort .typeError) from
    fun ⟨clock, error⟩ => targetSafe clock error, if_false]
  rw [terminatingEq, tracesEq]

end Flapjack.Compiler.Backend.ClosSem
