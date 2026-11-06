import Flapjack.Compiler.Backend.ClosNumber.Proofs.Install
import Flapjack.Compiler.Backend.ClosNumber.Proofs.EvaluateCases

/-! Dynamic installation in the closure-numbering evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Continuation after the closure evaluator has evaluated install arguments. -/
noncomputable def runInstalled {C F : Type} (values : List Value) (state : State C F) : EvalResult C F :=
  match doInstall values state with
  | (.err error, next) => (.err error, next)
  | (.val program, next) =>
    let (result, last) := evaluate program [] next
    match result with
    | .err error => (.err error, last)
    | .val values => (.val [@holLast Value ⟨unitValue⟩ values], last)

/-- The installation operator evaluates its arguments before the dynamic
compiler and installed program. -/
theorem evaluate_install_eq {C F : Type} (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (env : List Value) (state : State C F) :
    evaluate [.op trace .install args] env state =
      match evaluate args env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => runInstalled values.reverse next := by
  rw [evaluate, fixClock_evaluate]
  cases evaluated : evaluate args env state with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values =>
      dsimp only
      unfold runInstalled
      split <;> simp_all
      split <;> simp_all
      rfl

/-- Related nonempty value lists have related HOL last elements. -/
theorem holLast_related (maxApp : Nat) {left right : List Value}
    (related : List.Forall₂ (ValueRel maxApp) left right) (nonempty : left ≠ []) :
    ValueRel maxApp (@holLast Value ⟨unitValue⟩ left) (@holLast Value ⟨unitValue⟩ right) := by
  induction related with
  | nil => exact (nonempty rfl).elim
  | @cons first nextFirst rest nextRest head tail ih =>
    cases tail with
    | nil => simpa [holLast] using head
    | @cons second nextSecond tail nextTail nextHead restRel =>
      simp only [holLast]
      exact ih (by simp)

/-- The location marker inserted by incremental numbering evaluates without
changing the state and is prepended to successful program results. -/
theorem evaluate_location_prefix {C F : Type} (number : Nat) (expressions : List ClosLang.Exp)
    (state : State C F) :
    evaluate (.op .none (.intOp (.const (Int.ofNat number))) [] :: expressions) [] state =
      match evaluate expressions [] state with
      | (.err error, last) => (.err error, last)
      | (.val values, last) => (.val (.number number :: values), last) := by
  apply ClosProps.evaluate_cons_value
  simp [evaluate, fixClock, doApp, applyNumeric, doIntApp]

/-- Evaluate an installed program after its location marker, preserving the
observable result and final state. The program simulation is the induction
hypothesis for the enclosing installation case. -/
theorem evaluate_installed_program {C F : Type} (number : Nat) (expressions : List ClosLang.Exp)
    (source : State (Nat × C) F) (target : State C F)
    (result : Result (List Value) Value) (final : State (Nat × C) F)
    (run : evaluate expressions [] source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (nonempty : expressions ≠ []) (safe : ¬ ClosProps.containsAppSome source.maxApp expressions)
    (states : StateRel source target) (programIH : EvalSimulationAt source expressions) :
    ∃ targetResult targetFinal,
      evaluate (compileInc number expressions).2 [] target = (targetResult, targetFinal) ∧
      StateRel final targetFinal ∧
      match result, targetResult with
      | .err left, .err right => ResultRel source.maxApp (.err left) (.err right)
      | .val left, .val right =>
        ValueRel source.maxApp (@holLast Value ⟨unitValue⟩ left) (@holLast Value ⟨unitValue⟩ right)
      | _, _ => False := by
  let start := let next := number + max expressions.length 1
    if next % 2 = 0 then next else next + 1
  obtain ⟨targetResult, targetFinal, targetRun, resultRel, finalRel⟩ :=
    programIH [] [] target result final start run notType safe .nil states
  have numbered : (compileInc number expressions).2 =
      .op .none (.intOp (.const (Int.ofNat number))) [] :: (renumberList start expressions).2 := by
    simp [compileInc, start]
  have targetPrefix := evaluate_location_prefix number (renumberList start expressions).2 target
  rw [targetRun] at targetPrefix
  cases result with
  | err error =>
    cases targetResult with
    | val values => cases error <;> simp [ResultRel] at resultRel
    | err targetError =>
      refine ⟨.err targetError, targetFinal, ?_, finalRel, resultRel⟩
      simpa [numbered] using targetPrefix
  | val values =>
    cases targetResult with
    | err error => cases error <;> simp [ResultRel] at resultRel
    | val nextValues =>
      have valuesNonempty : values ≠ [] := by
        intro empty
        subst values
        have length := (evaluate_length (C := Nat × C) (F := F)).1 expressions [] source final [] run
        have : expressions = [] := List.eq_nil_of_length_eq_zero length.symm
        exact nonempty this
      have nextNonempty : nextValues ≠ [] := by
        intro empty
        subst nextValues
        have length := (show List.Forall₂ (ValueRel source.maxApp) values [] from resultRel).length_eq
        exact valuesNonempty (List.eq_nil_of_length_eq_zero length)
      refine ⟨.val (.number number :: nextValues), targetFinal, ?_, finalRel, ?_⟩
      · simpa [numbered] using targetPrefix
      · dsimp only
        let _ : Nonempty Value := ⟨unitValue⟩
        rw [holLast_cons, if_neg nextNonempty]
        exact holLast_related source.maxApp resultRel valuesNonempty

/-- Simulate the complete installation continuation using an induction
hypothesis for the program obtained from the compile oracle. -/
theorem runInstalled_related {C F : Type} (source : State (Nat × C) F) (target : State C F)
    (values nextValues : List Value) (result : Result (List Value) Value) (final : State (Nat × C) F)
    (run : runInstalled values source = (result, final))
    (notType : result ≠ .err (.abort .typeError))
    (states : StateRel source target) (valuesRel : List.Forall₂ (ValueRel source.maxApp) values nextValues)
    (programIH : ∀ expressions, EvalSimulationBelow (C := C) (F := F) source.clock expressions) :
    ∃ targetResult targetFinal, runInstalled nextValues target = (targetResult, targetFinal) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel final targetFinal := by
  cases installRun : doInstall values source with
  | mk installResult installed =>
    have installNotType : installResult ≠ .err (.abort .typeError) := by
      intro bad
      rw [bad] at installRun
      simp [runInstalled, installRun] at run
      exact notType run.1.symm
    obtain ⟨expressions, targetInstalled, targetInstall, sourceResult, safe, maxEq, installedRel⟩ :=
      doInstall_related source target values nextValues installResult installed states valuesRel installRun installNotType
    by_cases zero : source.clock = 0
    · simp only [zero, ↓reduceIte] at sourceResult targetInstall
      rw [sourceResult] at installRun
      simp only [runInstalled, installRun] at run
      cases run
      exact ⟨.err (.abort .timeoutError), targetInstalled, by simp [runInstalled, targetInstall], rfl, installedRel⟩
    · simp only [zero, ↓reduceIte] at sourceResult targetInstall
      rw [sourceResult] at installRun
      have clockLess : installed.clock < source.clock := by
        have clock := doInstall_success_clock values source installed expressions installRun
        omega
      have nonempty : expressions ≠ [] := by
        obtain ⟨_, _, _, _, _, program, _, _, _, _, _, _, _, _, _, _, programNonempty, _, resultEq⟩ :=
          doInstall_nonType_parts values source installed (.val expressions) installRun (by simp)
        simp only [zero, ↓reduceIte, Result.val.injEq] at resultEq
        simpa [resultEq] using programNonempty
      cases bodyRun : evaluate expressions [] installed with
      | mk bodyResult bodyFinal =>
        have bodyNotType : bodyResult ≠ .err (.abort .typeError) := by
          intro bad
          rw [bad] at bodyRun
          simp [runInstalled, installRun, bodyRun] at run
          exact notType run.1.symm
        obtain ⟨targetBodyResult, targetFinal, targetBodyRun, finalRel, resultRel⟩ :=
          evaluate_installed_program (source.compileOracle 0).1.1 expressions installed targetInstalled
            bodyResult bodyFinal bodyRun bodyNotType nonempty (by simpa [maxEq] using safe)
            installedRel (programIH expressions installed clockLess)
        cases bodyResult with
        | err error =>
          cases targetBodyResult with
          | val targetValues => simp at resultRel
          | err targetError =>
            simp only [runInstalled, installRun, bodyRun] at run
            cases run
            refine ⟨.err targetError, targetFinal, ?_, ?_, finalRel⟩
            · simp [runInstalled, targetInstall, targetBodyRun]
            · simpa [maxEq] using resultRel
        | val bodyValues =>
          cases targetBodyResult with
          | err targetError => simp at resultRel
          | val targetValues =>
            simp only [runInstalled, installRun, bodyRun] at run
            cases run
            refine ⟨.val [@holLast Value ⟨unitValue⟩ targetValues], targetFinal, ?_, ?_, finalRel⟩
            · simp [runInstalled, targetInstall, targetBodyRun]
            · exact .cons (by simpa [maxEq] using resultRel) .nil

/-- Installation expressions preserve the numbering simulation, assuming
the simulations for their arguments and dynamically installed program. The
general evaluator induction and HOL carrier review are still required. -/
theorem evaluate_install_step {C F : Type} (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (env nextEnv : List Value) (source : State (Nat × C) F) (target : State C F)
    (argsIH : EvalSimulationAt source args)
    (result : Result (List Value) Value) (sourceNext : State (Nat × C) F) (start : Nat)
    (run : evaluate [.op trace .install args] env source = (result, sourceNext))
    (noType : result ≠ .err (.abort .typeError))
    (safe : ¬ ClosProps.containsAppSome source.maxApp [.op trace .install args])
    (envRel : List.Forall₂ (ValueRel source.maxApp) env nextEnv) (stateRel : StateRel source target)
    (programIH : ∀ expressions, EvalSimulationBelow (C := C) (F := F) source.clock expressions) :
    ∃ targetResult targetNext,
      evaluate (renumberList start [.op trace .install args]).2 nextEnv target = (targetResult, targetNext) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext := by
  have argsSafe : ¬ ClosProps.containsAppSome source.maxApp args := by
    simpa [ClosProps.containsAppSome, ClosProps.containsAppSomeExp] using safe
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error =>
      rw [evaluate_install_eq, argsRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv target (.err error) sourceNext start argsRun noType argsSafe envRel stateRel
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [renumberList, renumber]
        rw [evaluate_install_eq, targetRun]
    | val values =>
      have argsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetMiddle, targetRun, valuesRel, middleRel⟩ :=
        argsIH env nextEnv target (.val values) middle start argsRun argsNoType argsSafe envRel stateRel
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at valuesRel
      | val nextValues =>
        have middleMax : middle.maxApp = source.maxApp := by
          have h := (ClosProps.evaluate_const (C := Nat × C) (F := F)).1 args env source
          simpa [argsRun] using h
        have related : List.Forall₂ (ValueRel middle.maxApp) values.reverse nextValues.reverse := by
          simpa [ResultRel, middleMax] using List.rel_reverse valuesRel
        have clockLe : middle.clock ≤ source.clock := by
          have h := evaluate_clock_le args env source
          simpa [argsRun] using h
        have smallerIH : ∀ expressions, EvalSimulationBelow (C := C) (F := F) middle.clock expressions := by
          intro expressions state smaller
          exact programIH expressions state (Nat.lt_of_lt_of_le smaller clockLe)
        rw [evaluate_install_eq, argsRun] at run
        obtain ⟨targetResult, targetFinal, targetInstall, resultRel, finalRel⟩ :=
          runInstalled_related middle targetMiddle values.reverse nextValues.reverse result sourceNext
            run noType middleRel related smallerIH
        refine ⟨targetResult, targetFinal, ?_, ?_, finalRel⟩
        · simp only [renumberList, renumber]
          rw [evaluate_install_eq, targetRun]
          exact targetInstall
        · simpa [middleMax] using resultRel

end Flapjack.Compiler.Backend.ClosNumber
