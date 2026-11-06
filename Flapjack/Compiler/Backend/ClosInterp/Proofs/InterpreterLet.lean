import Flapjack.Compiler.Backend.ClosInterp.Proofs.InterpreterIf

/-! Let-expression simulation for the proof-side interpreter. Its semantics
and state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- The let encoding selects list interpretation followed by body interpretation. -/
theorem interpreter_let_entry {C F : Type} (bindings body : ClosLang.Const)
    (env : List ClosSem.Value) (state : ClosSem.State C F) :
    let vars := [ClosSem.makeConst (.constCons 1 [bindings, body]), .block 0 [], ClosSem.listToValue env]
    let global := ClosLang.Exp.op .none (.globOp (.global 0)) []
    let bindingFirst := ClosLang.Exp.app .none none global [.var .none 2]
    let bindingSecond := ClosLang.Exp.app .none none bindingFirst [.op .none (.blockOp (.cons 1)) []]
    let bindingCall := ClosLang.Exp.app .none none bindingSecond [.op .none (.blockOp (.elemAt 0)) [.var .none 0]]
    let extended := ClosLang.Exp.op .none (.blockOp .listAppend) [.var .none 3, .var .none 0]
    let bodyFirst := ClosLang.Exp.app .none none global [extended]
    let bodySecond := ClosLang.Exp.app .none none bodyFirst [.op .none (.blockOp (.cons 0)) []]
    let bodyCall := ClosLang.Exp.app .none none bodySecond [.op .none (.blockOp (.elemAt 1)) [.var .none 1]]
    ClosSem.evaluate [closInterpreterBody] vars state =
      ClosSem.evaluate [.let .none [bindingCall] bodyCall] vars state := by
  dsimp only
  let vars := [ClosSem.makeConst (.constCons 1 [bindings, body]), ClosSem.Value.block 0 [], ClosSem.listToValue env]
  change ClosSem.evaluate [closInterpreterBody] vars state = _
  simp only [closInterpreterBody, interpreterIsCase_eq, interpreterVar_eq, interpreterGetEl_eq,
    interpreterCall_eq, interpreterCallList_eq, interpreterApp_eq]
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
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 1 2)) [.var .none 0]) _ _ vars state true (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.trueTag])]
  simp only [↓reduceIte]
  rfl

/-- An error while interpreting bindings prevents the body from running. -/
theorem interpreter_let_bindings_error {C F : Type} (source target targetFinal : ClosSem.State C F)
    (related : StateRel source target) (bindings body : ClosLang.Const) (env : List ClosSem.Value)
    (error : ErrorResult ClosSem.Value) (clock : 3 ≤ target.clock)
    (bindingsRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst bindings, .block 1 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) =
      (.err error, targetFinal)) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons 1 [bindings, body]), .block 0 [], ClosSem.listToValue env] target =
      (.err error, targetFinal) := by
  rw [interpreter_let_entry bindings body env target]
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  have call := evaluate_interpreter_field_call source target related 1 0 [bindings, body] bindings (by simp)
    (.block 0 []) env true clock
  simp only [↓reduceIte] at call
  rw [call, bindingsRun]

/-- Successful bindings extend the environment before the body call. -/
theorem interpreter_let_bindings_value {C F : Type}
    (source sourceMid target targetMid targetFinal : ClosSem.State C F)
    (related : StateRel source target) (midRelated : StateRel sourceMid targetMid)
    (bindings body : ClosLang.Const) (env values : List ClosSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (clock : 3 ≤ target.clock) (midClock : 3 ≤ targetMid.clock)
    (bindingsRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst bindings, .block 1 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) =
      (.val [ClosSem.listToValue values], targetMid))
    (bodyRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst body, .block 0 [], ClosSem.listToValue (values ++ env)]
      (ClosSem.decClock 3 targetMid) = (result, targetFinal)) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons 1 [bindings, body]), .block 0 [], ClosSem.listToValue env] target =
      (result, targetFinal) := by
  rw [interpreter_let_entry bindings body env target]
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  have call := evaluate_interpreter_field_call source target related 1 0 [bindings, body] bindings (by simp)
    (.block 0 []) env true clock
  simp only [↓reduceIte] at call
  rw [call, bindingsRun]
  let vars := [ClosSem.listToValue values, ClosSem.makeConst (.constCons 1 [bindings, body]),
    ClosSem.Value.block 0 [], ClosSem.listToValue env]
  let extended := ClosLang.Exp.op .none (.blockOp .listAppend) [.var .none 3, .var .none 0]
  let flag := ClosLang.Exp.op .none (.blockOp (.cons 0)) []
  let code := ClosLang.Exp.op .none (.blockOp (.elemAt 1)) [.var .none 1]
  have environmentRun : ClosSem.evaluate [extended] vars targetMid =
      (.val [ClosSem.listToValue (values ++ env)], targetMid) := by
    simp [extended, vars, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.valueToList_listToValue]
  have flagRun : ClosSem.evaluate [flag] vars targetMid = (.val [.block 0 []], targetMid) := by
    simp [flag, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock]
  have codeRun : ClosSem.evaluate [code] vars targetMid = (.val [ClosSem.makeConst body], targetMid) := by
    simp [code, vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock]
  have bodyCall := evaluate_interpreter_call sourceMid targetMid midRelated vars extended flag code
    (ClosSem.listToValue (values ++ env)) (.block 0 []) (ClosSem.makeConst body)
    environmentRun flagRun codeRun midClock
  change ClosSem.evaluate [.app .none none
    (.app .none none (.app .none none (.op .none (.globOp (.global 0)) []) [extended]) [flag]) [code]] vars targetMid = _
  rw [bodyCall, bodyRun]

/-- Let case of the proof-side interpreter simulation. -/
theorem interpreter_correct_let {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (bindingsIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate bindings env source = (result, sourceFinal) → canInterpretList bindings = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstantList bindings), .block 1 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } =
          (match result with
           | .err error => .err error
           | .val values => .val [ClosSem.listToValue values], targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (bodyIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [body] env source = (result, sourceFinal) → canInterpret body = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant body), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.let trace bindings body] env source = (result, sourceFinal))
    (valid : canInterpret (.let trace bindings body) = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant (.let trace bindings body)), .block 0 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  have parts : canInterpretList bindings = true ∧ canInterpret body = true := by
    simpa [canInterpret, Bool.and_eq_true, and_comm] using valid
  cases bindingsRun : ClosSem.evaluate bindings env source with
  | mk bindingResult sourceMid =>
    cases bindingResult with
    | err error =>
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bindingsRun] at run
      simp at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨extra, targetFinal, targetRun, finalRel⟩ :=
        bindingsIH env source target sourceMid (.err error) bindingsRun parts.1 assumption related notTypeError
      let enlarged := { target with clock := 3 + (extra + target.clock) }
      have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged :=
        stateRel_withClock related enlarged.clock
      have enough : 3 ≤ enlarged.clock := by simp [enlarged]
      have clocks : ClosSem.decClock 3 enlarged = { target with clock := extra + target.clock } := by
        simp [ClosSem.decClock, enlarged]
      have targetRun' : ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstantList bindings), .block 1 [], ClosSem.listToValue env]
          (ClosSem.decClock 3 enlarged) = (.err error, targetFinal) := by
        simpa only [clocks] using targetRun
      have reduction := interpreter_let_bindings_error { source with clock := enlarged.clock } enlarged targetFinal
        enlargedRel (toConstantList bindings) (toConstant body) env error enough targetRun'
      refine ⟨3 + extra, targetFinal, ?_, finalRel⟩
      simpa [toConstant, enlarged, Nat.add_assoc] using reduction
    | val values =>
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bindingsRun] at run
      obtain ⟨bindingExtra, targetMid, targetBindings, midRel⟩ :=
        bindingsIH env source target sourceMid (.val values) bindingsRun parts.1 assumption related (by simp)
      have sourceBound : sourceMid.clock ≤ source.clock := by
        have bound := ClosSem.evaluate_clock_le bindings env source
        simpa [bindingsRun] using bound
      obtain ⟨bodyExtra, targetFinal, targetBody, finalRel⟩ :=
        bodyIH (values ++ env) sourceMid targetMid sourceFinal result run parts.2
          (interpAssum_le assumption sourceBound) midRel notTypeError
      let offset := 3 + bodyExtra
      let enlarged := { target with clock := 3 + ((bindingExtra + target.clock) + offset) }
      let enlargedMid := { targetMid with clock := targetMid.clock + offset }
      have shiftedBindings := ClosSem.evaluate_addClock.1 [closInterpreterBody]
        [ClosSem.makeConst (toConstantList bindings), .block 1 [], ClosSem.listToValue env]
        { target with clock := bindingExtra + target.clock } targetMid (.val [ClosSem.listToValue values])
        offset targetBindings (by simp)
      have bindingsRun' : ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstantList bindings), .block 1 [], ClosSem.listToValue env]
          (ClosSem.decClock 3 enlarged) = (.val [ClosSem.listToValue values], enlargedMid) := by
        simpa [ClosSem.decClock, enlarged, enlargedMid] using shiftedBindings
      have bodyRun' : ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant body), .block 0 [], ClosSem.listToValue (values ++ env)]
          (ClosSem.decClock 3 enlargedMid) = (result, targetFinal) := by
        have clocks : ClosSem.decClock 3 enlargedMid =
            { targetMid with clock := bodyExtra + targetMid.clock } := by
          simp only [ClosSem.decClock, enlargedMid, offset]
          congr 1
          omega
        rw [clocks]
        exact targetBody
      have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged :=
        stateRel_withClock related enlarged.clock
      have enlargedMidRel : StateRel { sourceMid with clock := enlargedMid.clock } enlargedMid :=
        stateRel_withClock midRel enlargedMid.clock
      have enough : 3 ≤ enlarged.clock := by simp [enlarged]
      have midEnough : 3 ≤ enlargedMid.clock := by simp [enlargedMid, offset]; omega
      have reduction := interpreter_let_bindings_value { source with clock := enlarged.clock }
        { sourceMid with clock := enlargedMid.clock } enlarged enlargedMid targetFinal enlargedRel enlargedMidRel
        (toConstantList bindings) (toConstant body) env values result enough midEnough bindingsRun' bodyRun'
      refine ⟨3 + (bindingExtra + offset), targetFinal, ?_, finalRel⟩
      simpa [toConstant, enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reduction

end Flapjack.Compiler.Backend.ClosInterp
