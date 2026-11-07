import Flapjack.Compiler.Backend.ClosInterp.Proofs.InterpreterList

/-! Conditional-expression simulation for the proof-side interpreter. Its
semantics and state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- The conditional encoding dispatches to three recursive calls. -/
theorem interpreter_if_entry {C F : Type} (condition yes no : ClosLang.Const)
    (env : List ClosSem.Value) (state : ClosSem.State C F) :
    let vars := [ClosSem.makeConst (.constCons 0 [condition, yes, no]), .block 0 [], ClosSem.listToValue env]
    let global := ClosLang.Exp.op .none (.globOp (.global 0)) []
    let first := ClosLang.Exp.app .none none global [.var .none 2]
    let second := ClosLang.Exp.app .none none first [.op .none (.blockOp (.cons 0)) []]
    let call := fun index => ClosLang.Exp.app .none none second [.op .none (.blockOp (.elemAt index)) [.var .none 0]]
    ClosSem.evaluate [closInterpreterBody] vars state =
      ClosSem.evaluate [.ifThenElse .none (call 0) (call 1) (call 2)] vars state := by
  dsimp only
  let vars := [ClosSem.makeConst (.constCons 0 [condition, yes, no]), ClosSem.Value.block 0 [], ClosSem.listToValue env]
  change ClosSem.evaluate [closInterpreterBody] vars state = _
  simp only [closInterpreterBody, interpreterIsCase_eq, interpreterVar_eq, interpreterGetEl_eq,
    interpreterCall_eq, interpreterApp_eq]
  rw [evaluate_if_condition (.var .none 1) _ _ vars state false (by
    simp [vars, ClosSem.evaluate, ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 0 2)) [.var .none 0]) _ _ vars state false (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 1 1)) [.var .none 0]) _ _ vars state false (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 2 1)) [.var .none 0]) _ _ vars state false (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 0 1)) [.var .none 0]) _ _ vars state false (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 1 2)) [.var .none 0]) _ _ vars state false (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 2 2)) [.var .none 0]) _ _ vars state false (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 0 3)) [.var .none 0]) _ _ vars state true (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.trueTag])]
  simp only [↓reduceIte]
  rfl

/-- A failing condition is propagated without interpreting either branch. -/
theorem interpreter_if_condition_error {C F : Type} (source target targetFinal : ClosSem.State C F)
    (related : StateRel source target) (condition yes no : ClosLang.Const) (env : List ClosSem.Value)
    (error : ErrorResult ClosSem.Value) (clock : 3 ≤ target.clock)
    (conditionRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst condition, .block 0 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) =
      (.err error, targetFinal)) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons 0 [condition, yes, no]), .block 0 [], ClosSem.listToValue env] target =
      (.err error, targetFinal) := by
  rw [interpreter_if_entry condition yes no env target]
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  have call := evaluate_interpreter_field_call source target related 0 0 [condition, yes, no] condition (by simp)
    (.block 0 []) env false clock
  simp only [Bool.false_eq_true, ↓reduceIte] at call
  rw [call, conditionRun]

/-- A Boolean condition selects the corresponding recursive branch. -/
theorem interpreter_if_condition_value {C F : Type}
    (source sourceMid target targetMid targetFinal : ClosSem.State C F)
    (related : StateRel source target) (midRelated : StateRel sourceMid targetMid)
    (condition yes no : ClosLang.Const) (env : List ClosSem.Value) (choice : Bool)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (clock : 3 ≤ target.clock) (midClock : 3 ≤ targetMid.clock)
    (conditionRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst condition, .block 0 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) =
      (.val [ClosSem.boolValue choice], targetMid))
    (branchRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (if choice then yes else no), .block 0 [], ClosSem.listToValue env]
      (ClosSem.decClock 3 targetMid) = (result, targetFinal)) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons 0 [condition, yes, no]), .block 0 [], ClosSem.listToValue env] target =
      (result, targetFinal) := by
  rw [interpreter_if_entry condition yes no env target]
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  have call := evaluate_interpreter_field_call source target related 0 0 [condition, yes, no] condition (by simp)
    (.block 0 []) env false clock
  simp only [Bool.false_eq_true, ↓reduceIte] at call
  rw [call, conditionRun]
  cases choice with
  | false =>
    simp only [ClosSem.asBool, ClosSem.boolValue, BackendCommon.falseTag]
    have branch := evaluate_interpreter_field_call sourceMid targetMid midRelated 0 2 [condition, yes, no] no (by simp)
      (.block 0 []) env false midClock
    simp only [Bool.false_eq_true, ↓reduceIte] at branch
    rw [branch]
    simpa using branchRun
  | true =>
    simp only [ClosSem.asBool, ClosSem.boolValue, BackendCommon.trueTag, ↓reduceIte]
    have branch := evaluate_interpreter_field_call sourceMid targetMid midRelated 0 1 [condition, yes, no] yes (by simp)
      (.block 0 []) env false midClock
    simp only [Bool.false_eq_true, ↓reduceIte] at branch
    rw [branch]
    simpa using branchRun

/-- Conditional simulation after a Boolean condition, assuming the
condition and chosen-branch simulations. -/
theorem interpreter_correct_if_value {C F : Type} (condition yes no : ClosLang.Exp) (choice : Bool)
    (conditionIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [condition] env source = (result, sourceFinal) →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant condition), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (branchIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [if choice then yes else no] env source = (result, sourceFinal) →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant (if choice then yes else no)), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source sourceMid sourceFinal target : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (conditionRun : ClosSem.evaluate [condition] env source = (.val [ClosSem.boolValue choice], sourceMid))
    (branchRun : ClosSem.evaluate [if choice then yes else no] env sourceMid = (result, sourceFinal))
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (.constCons 0 [toConstant condition, toConstant yes, toConstant no]),
          .block 0 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  obtain ⟨conditionExtra, targetMid, targetCondition, midRel⟩ :=
    conditionIH env source target sourceMid (.val [ClosSem.boolValue choice]) conditionRun assumption related (by simp)
  have sourceBound : sourceMid.clock ≤ source.clock := by
    have bound := ClosSem.evaluate_clock_le [condition] env source
    simpa [conditionRun] using bound
  obtain ⟨branchExtra, targetFinal, targetBranch, finalRel⟩ :=
    branchIH env sourceMid targetMid sourceFinal result branchRun (interpAssum_le assumption sourceBound) midRel notTypeError
  let offset := 3 + branchExtra
  let enlarged := { target with clock := 3 + ((conditionExtra + target.clock) + offset) }
  let enlargedMid := { targetMid with clock := targetMid.clock + offset }
  have shiftedCondition := ClosSem.evaluate_addClock.1 [closInterpreterBody]
    [ClosSem.makeConst (toConstant condition), .block 0 [], ClosSem.listToValue env]
    { target with clock := conditionExtra + target.clock } targetMid (.val [ClosSem.boolValue choice])
    offset targetCondition (by simp)
  have conditionRun' : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstant condition), .block 0 [], ClosSem.listToValue env]
      (ClosSem.decClock 3 enlarged) = (.val [ClosSem.boolValue choice], enlargedMid) := by
    simpa [ClosSem.decClock, enlarged, enlargedMid] using shiftedCondition
  have branchRun' : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (if choice then toConstant yes else toConstant no), .block 0 [], ClosSem.listToValue env]
      (ClosSem.decClock 3 enlargedMid) = (result, targetFinal) := by
    have clocks : ClosSem.decClock 3 enlargedMid =
        { targetMid with clock := branchExtra + targetMid.clock } := by
      simp only [ClosSem.decClock, enlargedMid, offset]
      congr 1
      omega
    rw [clocks]
    cases choice <;> simpa using targetBranch
  have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged :=
    stateRel_withClock related enlarged.clock
  have enlargedMidRel : StateRel { sourceMid with clock := enlargedMid.clock } enlargedMid :=
    stateRel_withClock midRel enlargedMid.clock
  have enough : 3 ≤ enlarged.clock := by simp [enlarged]
  have midEnough : 3 ≤ enlargedMid.clock := by simp [enlargedMid, offset]; omega
  have reduction := interpreter_if_condition_value { source with clock := enlarged.clock }
    { sourceMid with clock := enlargedMid.clock } enlarged enlargedMid targetFinal enlargedRel enlargedMidRel
    (toConstant condition) (toConstant yes) (toConstant no) env choice result enough midEnough conditionRun' branchRun'
  refine ⟨3 + (conditionExtra + offset), targetFinal, ?_, finalRel⟩
  simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reduction

/-- The Boolean decoder only accepts the two Boolean value constructors. -/
theorem asBool_eq_some_value (value : ClosSem.Value) (choice : Bool)
    (decoded : ClosSem.asBool value = some choice) : value = ClosSem.boolValue choice := by
  cases value with
  | block tag fields =>
    cases tag with
    | zero =>
      cases fields <;> simp [ClosSem.asBool, ClosSem.boolValue, BackendCommon.falseTag, BackendCommon.trueTag] at decoded ⊢
      subst choice
      rfl
    | succ tag =>
      cases tag with
      | zero =>
        cases fields <;> simp [ClosSem.asBool, ClosSem.boolValue, BackendCommon.trueTag, BackendCommon.falseTag] at decoded ⊢
        subst choice
        rfl
      | succ tag => simp [ClosSem.asBool] at decoded
  | _ => simp [ClosSem.asBool] at decoded

/-- Conditional case of the proof-side interpreter simulation. -/
theorem interpreter_correct_if {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp)
    (conditionIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [condition] env source = (result, sourceFinal) → canInterpret condition = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant condition), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (yesIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [yes] env source = (result, sourceFinal) → canInterpret yes = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant yes), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (noIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [no] env source = (result, sourceFinal) → canInterpret no = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant no), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.ifThenElse trace condition yes no] env source = (result, sourceFinal))
    (valid : canInterpret (.ifThenElse trace condition yes no) = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant (.ifThenElse trace condition yes no)), .block 0 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  have parts : canInterpret condition = true ∧ canInterpret yes = true ∧ canInterpret no = true := by
    simpa [canInterpret, Bool.and_eq_true, and_assoc] using valid
  cases conditionRun : ClosSem.evaluate [condition] env source with
  | mk conditionResult sourceMid =>
    cases conditionResult with
    | err error =>
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, conditionRun] at run
      simp at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨extra, targetFinal, targetRun, finalRel⟩ :=
        conditionIH env source target sourceMid (.err error) conditionRun parts.1 assumption related notTypeError
      let enlarged := { target with clock := 3 + (extra + target.clock) }
      have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged :=
        stateRel_withClock related enlarged.clock
      have enough : 3 ≤ enlarged.clock := by simp [enlarged]
      have clocks : ClosSem.decClock 3 enlarged = { target with clock := extra + target.clock } := by
        simp [ClosSem.decClock, enlarged]
      have targetRun' : ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant condition), .block 0 [], ClosSem.listToValue env]
          (ClosSem.decClock 3 enlarged) = (.err error, targetFinal) := by
        simpa only [clocks] using targetRun
      have reduction := interpreter_if_condition_error { source with clock := enlarged.clock } enlarged targetFinal
        enlargedRel (toConstant condition) (toConstant yes) (toConstant no) env error enough targetRun'
      refine ⟨3 + extra, targetFinal, ?_, finalRel⟩
      simpa [toConstant, enlarged, Nat.add_assoc] using reduction
    | val values =>
      obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value condition env source sourceMid values conditionRun
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, conditionRun] at run
      change (match ClosSem.asBool value with
        | none => (.err (.abort .typeError), sourceMid)
        | some true => ClosSem.evaluate [yes] env sourceMid
        | some false => ClosSem.evaluate [no] env sourceMid) = (result, sourceFinal) at run
      cases decoded : ClosSem.asBool value with
      | none =>
        rw [decoded] at run
        simp at run
        exact (notTypeError run.1.symm).elim
      | some choice =>
        have valueEq := asBool_eq_some_value value choice decoded
        subst value
        rw [decoded] at run
        cases choice with
        | false =>
          apply interpreter_correct_if_value condition yes no false ?_ ?_ env source sourceMid sourceFinal target result
            conditionRun run assumption related notTypeError
          · intro env source target sourceFinal result run assumption related notTypeError
            exact conditionIH env source target sourceFinal result run parts.1 assumption related notTypeError
          · intro env source target sourceFinal result run assumption related notTypeError
            exact noIH env source target sourceFinal result run parts.2.2 assumption related notTypeError
        | true =>
          apply interpreter_correct_if_value condition yes no true ?_ ?_ env source sourceMid sourceFinal target result
            conditionRun run assumption related notTypeError
          · intro env source target sourceFinal result run assumption related notTypeError
            exact conditionIH env source target sourceFinal result run parts.1 assumption related notTypeError
          · intro env source target sourceFinal result run assumption related notTypeError
            exact yesIH env source target sourceFinal result run parts.2.1 assumption related notTypeError

end Flapjack.Compiler.Backend.ClosInterp
