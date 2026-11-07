import Flapjack.Compiler.Backend.ClosInterp.Proofs.InterpreterHandle

/-! Application-expression simulation for the proof-side interpreter. Its
semantics and state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- The application encoding selects recursive calls for function and argument. -/
theorem interpreter_app_entry {C F : Type} (function argument : ClosLang.Const)
    (env : List ClosSem.Value) (state : ClosSem.State C F) :
    let vars := [ClosSem.makeConst (.constCons 0 [function, argument]), .block 0 [], ClosSem.listToValue env]
    let global := ClosLang.Exp.op .none (.globOp (.global 0)) []
    let first := ClosLang.Exp.app .none none global [.var .none 2]
    let second := ClosLang.Exp.app .none none first [.op .none (.blockOp (.cons 0)) []]
    let call := fun index => ClosLang.Exp.app .none none second [.op .none (.blockOp (.elemAt index)) [.var .none 0]]
    ClosSem.evaluate [closInterpreterBody] vars state =
      ClosSem.evaluate [.app .none none (call 0) [call 1]] vars state := by
  dsimp only
  let vars := [ClosSem.makeConst (.constCons 0 [function, argument]), ClosSem.Value.block 0 [], ClosSem.listToValue env]
  change ClosSem.evaluate [closInterpreterBody] vars state = _
  simp only [closInterpreterBody, interpreterIsCase_eq, interpreterVar_eq, interpreterGetEl_eq,
    interpreterCall_eq, interpreterApp_eq]
  rw [evaluate_if_condition (.var .none 1) _ _ vars state false (by
    simp [vars, ClosSem.evaluate, ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 0 2)) [.var .none 0]) _ _ vars state true (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.trueTag])]
  simp only [↓reduceIte]
  rfl

/-- An argument error is propagated before the function is interpreted. -/
theorem interpreter_app_argument_error {C F : Type} (source target targetFinal : ClosSem.State C F)
    (related : StateRel source target) (function argument : ClosLang.Const) (env : List ClosSem.Value)
    (error : ErrorResult ClosSem.Value) (clock : 3 ≤ target.clock)
    (argumentRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst argument, .block 0 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) =
      (.err error, targetFinal)) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons 0 [function, argument]), .block 0 [], ClosSem.listToValue env] target =
      (.err error, targetFinal) := by
  rw [interpreter_app_entry function argument env target]
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
  have call := evaluate_interpreter_field_call source target related 0 1 [function, argument] argument (by simp)
    (.block 0 []) env false clock
  simp only [Bool.false_eq_true, ↓reduceIte] at call
  rw [call, argumentRun]

/-- After a successful argument, a function error is propagated. -/
theorem interpreter_app_function_error {C F : Type}
    (source sourceMid target targetMid targetFinal : ClosSem.State C F)
    (related : StateRel source target) (midRelated : StateRel sourceMid targetMid)
    (function argument : ClosLang.Const) (env : List ClosSem.Value) (value : ClosSem.Value)
    (error : ErrorResult ClosSem.Value) (clock : 3 ≤ target.clock) (midClock : 3 ≤ targetMid.clock)
    (argumentRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst argument, .block 0 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) =
      (.val [value], targetMid))
    (functionRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst function, .block 0 [], ClosSem.listToValue env] (ClosSem.decClock 3 targetMid) =
      (.err error, targetFinal)) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons 0 [function, argument]), .block 0 [], ClosSem.listToValue env] target =
      (.err error, targetFinal) := by
  rw [interpreter_app_entry function argument env target]
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
  have argCall := evaluate_interpreter_field_call source target related 0 1 [function, argument] argument (by simp)
    (.block 0 []) env false clock
  simp only [Bool.false_eq_true, ↓reduceIte] at argCall
  rw [argCall, argumentRun]
  rw [ClosSem.fixClock_evaluate]
  have functionCall := evaluate_interpreter_field_call sourceMid targetMid midRelated 0 0 [function, argument] function (by simp)
    (.block 0 []) env false midClock
  simp only [Bool.false_eq_true, ↓reduceIte] at functionCall
  rw [functionCall, functionRun]

/-- Successful recursive calls feed their values to closure application. -/
theorem interpreter_app_values {C F : Type}
    (source sourceMid target targetMid targetReady : ClosSem.State C F)
    (related : StateRel source target) (midRelated : StateRel sourceMid targetMid)
    (function argument : ClosLang.Const) (env : List ClosSem.Value) (value fn : ClosSem.Value)
    (clock : 3 ≤ target.clock) (midClock : 3 ≤ targetMid.clock)
    (argumentRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst argument, .block 0 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) =
      (.val [value], targetMid))
    (functionRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst function, .block 0 [], ClosSem.listToValue env] (ClosSem.decClock 3 targetMid) =
      (.val [fn], targetReady)) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons 0 [function, argument]), .block 0 [], ClosSem.listToValue env] target =
      ClosSem.evaluateApp none fn [value] targetReady := by
  rw [interpreter_app_entry function argument env target]
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
  have argCall := evaluate_interpreter_field_call source target related 0 1 [function, argument] argument (by simp)
    (.block 0 []) env false clock
  simp only [Bool.false_eq_true, ↓reduceIte] at argCall
  rw [argCall, argumentRun]
  rw [ClosSem.fixClock_evaluate]
  have functionCall := evaluate_interpreter_field_call sourceMid targetMid midRelated 0 0 [function, argument] function (by simp)
    (.block 0 []) env false midClock
  simp only [Bool.false_eq_true, ↓reduceIte] at functionCall
  rw [functionCall, functionRun]
  rfl

/-- Application simulation when the argument and function evaluations
succeed. Closure application uses the clock-bounded application hypothesis. -/
theorem interpreter_correct_app_values {C F : Type}
    (function argument : ClosLang.Exp)
    (argumentIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [argument] env source = (result, sourceFinal) →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant argument), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (functionIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [function] env source = (result, sourceFinal) →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant function), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source sourceMid sourceReady sourceFinal target : ClosSem.State C F)
    (value fn : ClosSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argumentRun : ClosSem.evaluate [argument] env source = (.val [value], sourceMid))
    (functionRun : ClosSem.evaluate [function] env sourceMid = (.val [fn], sourceReady))
    (applyRun : ClosSem.evaluateApp none fn [value] sourceReady = (result, sourceFinal))
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (.constCons 0 [toConstant function, toConstant argument]), .block 0 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  obtain ⟨argumentExtra, targetMid, targetArgument, midRel⟩ :=
    argumentIH env source target sourceMid (.val [value]) argumentRun assumption related (by simp)
  have midBound : sourceMid.clock ≤ source.clock := by
    have bound := ClosSem.evaluate_clock_le [argument] env source
    simpa [argumentRun] using bound
  obtain ⟨functionExtra, targetReady, targetFunction, readyRel⟩ :=
    functionIH env sourceMid targetMid sourceReady (.val [fn]) functionRun
      (interpAssum_le assumption midBound) midRel (by simp)
  have readyBound : sourceReady.clock ≤ source.clock := by
    have bound := ClosSem.evaluate_clock_le [function] env sourceMid
    simp only [functionRun] at bound
    omega
  obtain ⟨applyExtra, targetFinal, targetApply, finalRel⟩ :=
    assumption.2 [value] sourceReady none fn targetReady result sourceFinal readyBound applyRun notTypeError readyRel
  let offset := 3 + (functionExtra + applyExtra)
  let enlarged := { target with clock := 3 + ((argumentExtra + target.clock) + offset) }
  let enlargedMid := { targetMid with clock := targetMid.clock + offset }
  let enlargedReady := { targetReady with clock := targetReady.clock + applyExtra }
  have shiftedArgument := ClosSem.evaluate_addClock.1 [closInterpreterBody]
    [ClosSem.makeConst (toConstant argument), .block 0 [], ClosSem.listToValue env]
    { target with clock := argumentExtra + target.clock } targetMid (.val [value]) offset targetArgument (by simp)
  have argumentRun' : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstant argument), .block 0 [], ClosSem.listToValue env]
      (ClosSem.decClock 3 enlarged) = (.val [value], enlargedMid) := by
    simpa [ClosSem.decClock, enlarged, enlargedMid] using shiftedArgument
  have shiftedFunction := ClosSem.evaluate_addClock.1 [closInterpreterBody]
    [ClosSem.makeConst (toConstant function), .block 0 [], ClosSem.listToValue env]
    { targetMid with clock := functionExtra + targetMid.clock } targetReady (.val [fn])
    applyExtra targetFunction (by simp)
  have functionRun' : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstant function), .block 0 [], ClosSem.listToValue env]
      (ClosSem.decClock 3 enlargedMid) = (.val [fn], enlargedReady) := by
    have clocks : ClosSem.decClock 3 enlargedMid =
        { targetMid with clock := (functionExtra + targetMid.clock) + applyExtra } := by
      simp only [ClosSem.decClock, enlargedMid, offset]
      congr 1
      omega
    rw [clocks]
    simpa [enlargedReady] using shiftedFunction
  have applyRun' : ClosSem.evaluateApp none fn [value] enlargedReady = (result, targetFinal) := by
    simpa [enlargedReady, Nat.add_comm] using targetApply
  have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged :=
    stateRel_withClock related enlarged.clock
  have enlargedMidRel : StateRel { sourceMid with clock := enlargedMid.clock } enlargedMid :=
    stateRel_withClock midRel enlargedMid.clock
  have enough : 3 ≤ enlarged.clock := by simp [enlarged]
  have midEnough : 3 ≤ enlargedMid.clock := by simp [enlargedMid, offset]; omega
  have reduction := interpreter_app_values { source with clock := enlarged.clock }
    { sourceMid with clock := enlargedMid.clock } enlarged enlargedMid enlargedReady enlargedRel enlargedMidRel
    (toConstant function) (toConstant argument) env value fn enough midEnough argumentRun' functionRun'
  rw [applyRun'] at reduction
  refine ⟨3 + (argumentExtra + offset), targetFinal, ?_, finalRel⟩
  simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reduction

/-- Application simulation when the argument succeeds and the function fails. -/
theorem interpreter_correct_app_function_error {C F : Type}
    (function argument : ClosLang.Exp)
    (argumentIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [argument] env source = (result, sourceFinal) →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant argument), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (functionIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [function] env source = (result, sourceFinal) →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant function), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source sourceMid sourceFinal target : ClosSem.State C F)
    (value : ClosSem.Value) (error : ErrorResult ClosSem.Value)
    (argumentRun : ClosSem.evaluate [argument] env source = (.val [value], sourceMid))
    (functionRun : ClosSem.evaluate [function] env sourceMid = (.err error, sourceFinal))
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : (Result.err error : Result (List ClosSem.Value) ClosSem.Value) ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (.constCons 0 [toConstant function, toConstant argument]), .block 0 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (.err error, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  obtain ⟨argumentExtra, targetMid, targetArgument, midRel⟩ :=
    argumentIH env source target sourceMid (.val [value]) argumentRun assumption related (by simp)
  have midBound : sourceMid.clock ≤ source.clock := by
    have bound := ClosSem.evaluate_clock_le [argument] env source
    simpa [argumentRun] using bound
  obtain ⟨functionExtra, targetFinal, targetFunction, finalRel⟩ :=
    functionIH env sourceMid targetMid sourceFinal (.err error) functionRun
      (interpAssum_le assumption midBound) midRel notTypeError
  let offset := 3 + functionExtra
  let enlarged := { target with clock := 3 + ((argumentExtra + target.clock) + offset) }
  let enlargedMid := { targetMid with clock := targetMid.clock + offset }
  have shiftedArgument := ClosSem.evaluate_addClock.1 [closInterpreterBody]
    [ClosSem.makeConst (toConstant argument), .block 0 [], ClosSem.listToValue env]
    { target with clock := argumentExtra + target.clock } targetMid (.val [value]) offset targetArgument (by simp)
  have argumentRun' : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstant argument), .block 0 [], ClosSem.listToValue env]
      (ClosSem.decClock 3 enlarged) = (.val [value], enlargedMid) := by
    simpa [ClosSem.decClock, enlarged, enlargedMid] using shiftedArgument
  have functionRun' : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstant function), .block 0 [], ClosSem.listToValue env]
      (ClosSem.decClock 3 enlargedMid) = (.err error, targetFinal) := by
    have clocks : ClosSem.decClock 3 enlargedMid =
        { targetMid with clock := functionExtra + targetMid.clock } := by
      simp only [ClosSem.decClock, enlargedMid, offset]
      congr 1
      omega
    rw [clocks]
    exact targetFunction
  have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged :=
    stateRel_withClock related enlarged.clock
  have enlargedMidRel : StateRel { sourceMid with clock := enlargedMid.clock } enlargedMid :=
    stateRel_withClock midRel enlargedMid.clock
  have enough : 3 ≤ enlarged.clock := by simp [enlarged]
  have midEnough : 3 ≤ enlargedMid.clock := by simp [enlargedMid, offset]; omega
  have reduction := interpreter_app_function_error { source with clock := enlarged.clock }
    { sourceMid with clock := enlargedMid.clock } enlarged enlargedMid targetFinal enlargedRel enlargedMidRel
    (toConstant function) (toConstant argument) env value error enough midEnough argumentRun' functionRun'
  refine ⟨3 + (argumentExtra + offset), targetFinal, ?_, finalRel⟩
  simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reduction

/-- Unary application case of the proof-side interpreter simulation. -/
theorem interpreter_correct_unary_app {C F : Type} (trace : BackendCommon.Tra)
    (function argument : ClosLang.Exp)
    (argumentIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [argument] env source = (result, sourceFinal) → canInterpret argument = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant argument), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (functionIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [function] env source = (result, sourceFinal) → canInterpret function = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant function), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.app trace none function [argument]] env source = (result, sourceFinal))
    (valid : canInterpret (.app trace none function [argument]) = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant (.app trace none function [argument])), .block 0 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  have parts : canInterpret function = true ∧ canInterpret argument = true := by
    simpa [canInterpret, canInterpretList, Bool.and_eq_true] using valid
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
  cases argumentRun : ClosSem.evaluate [argument] env source with
  | mk argumentResult sourceMid =>
    rw [argumentRun] at run
    cases argumentResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨extra, targetFinal, targetRun, finalRel⟩ :=
        argumentIH env source target sourceMid (.err error) argumentRun parts.2 assumption related notTypeError
      let enlarged := { target with clock := 3 + (extra + target.clock) }
      have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged :=
        stateRel_withClock related enlarged.clock
      have enough : 3 ≤ enlarged.clock := by simp [enlarged]
      have clocks : ClosSem.decClock 3 enlarged = { target with clock := extra + target.clock } := by
        simp [ClosSem.decClock, enlarged]
      have targetRun' : ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant argument), .block 0 [], ClosSem.listToValue env]
          (ClosSem.decClock 3 enlarged) = (.err error, targetFinal) := by
        simpa only [clocks] using targetRun
      have reduction := interpreter_app_argument_error { source with clock := enlarged.clock } enlarged targetFinal
        enlargedRel (toConstant function) (toConstant argument) env error enough targetRun'
      refine ⟨3 + extra, targetFinal, ?_, finalRel⟩
      simpa [toConstant, enlarged, Nat.add_assoc] using reduction
    | val argumentValues =>
      obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value argument env source sourceMid argumentValues argumentRun
      dsimp only at run
      rw [ClosSem.fixClock_evaluate] at run
      cases functionRun : ClosSem.evaluate [function] env sourceMid with
      | mk functionResult sourceReady =>
        rw [functionRun] at run
        cases functionResult with
        | err error =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          have reduction := interpreter_correct_app_function_error function argument
            (fun env source target sourceFinal result run assumption related notTypeError =>
              argumentIH env source target sourceFinal result run parts.2 assumption related notTypeError)
            (fun env source target sourceFinal result run assumption related notTypeError =>
              functionIH env source target sourceFinal result run parts.1 assumption related notTypeError)
            env source sourceMid sourceReady target value error argumentRun functionRun assumption related notTypeError
          simpa [toConstant] using reduction
        | val functionValues =>
          obtain ⟨fn, rfl⟩ := ClosSem.evaluate_singleton_value function env sourceMid sourceReady functionValues functionRun
          change ClosSem.evaluateApp none fn [value] sourceReady = (result, sourceFinal) at run
          have reduction := interpreter_correct_app_values function argument
            (fun env source target sourceFinal result run assumption related notTypeError =>
              argumentIH env source target sourceFinal result run parts.2 assumption related notTypeError)
            (fun env source target sourceFinal result run assumption related notTypeError =>
              functionIH env source target sourceFinal result run parts.1 assumption related notTypeError)
            env source sourceMid sourceReady sourceFinal target value fn result argumentRun functionRun run assumption related notTypeError
          simpa [toConstant] using reduction

/-- Application case for the subset accepted by `canInterpret`. -/
theorem interpreter_correct_app {C F : Type} (trace : BackendCommon.Tra)
    (location : Option Nat) (function : ClosLang.Exp) (arguments : List ClosLang.Exp)
    (argumentIH : ∀ argument ∈ arguments, ∀ (env : List ClosSem.Value)
      (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [argument] env source = (result, sourceFinal) → canInterpret argument = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant argument), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (functionIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [function] env source = (result, sourceFinal) → canInterpret function = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant function), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.app trace location function arguments] env source = (result, sourceFinal))
    (valid : canInterpret (.app trace location function arguments) = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant (.app trace location function arguments)), .block 0 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  cases location with
  | some location => simp [canInterpret] at valid
  | none =>
    cases arguments with
    | nil => simp [canInterpret, canInterpretList] at valid
    | cons argument rest =>
      cases rest with
      | cons other rest => simp [canInterpret, canInterpretList] at valid
      | nil =>
        exact interpreter_correct_unary_app trace function argument (argumentIH argument (by simp)) functionIH
          env source target sourceFinal result run valid assumption related notTypeError

end Flapjack.Compiler.Backend.ClosInterp
