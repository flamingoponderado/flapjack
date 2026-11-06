import Flapjack.Compiler.Backend.ClosInterp.Proofs.InterpreterLet

/-! Exception-handler simulation for the proof-side interpreter. Its semantics
and state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- The handler encoding selects recursive calls for its body and handler. -/
theorem interpreter_handle_entry {C F : Type} (body handler : ClosLang.Const)
    (env : List ClosSem.Value) (state : ClosSem.State C F) :
    let vars := [ClosSem.makeConst (.constCons 2 [body, handler]), .block 0 [], ClosSem.listToValue env]
    let global := ClosLang.Exp.op .none (.globOp (.global 0)) []
    let bodyFirst := ClosLang.Exp.app .none none global [.var .none 2]
    let bodySecond := ClosLang.Exp.app .none none bodyFirst [.op .none (.blockOp (.cons 0)) []]
    let bodyCall := ClosLang.Exp.app .none none bodySecond [.op .none (.blockOp (.elemAt 0)) [.var .none 0]]
    let extended := ClosLang.Exp.op .none (.blockOp (.cons 0)) [.var .none 3, .var .none 0]
    let handlerFirst := ClosLang.Exp.app .none none global [extended]
    let handlerSecond := ClosLang.Exp.app .none none handlerFirst [.op .none (.blockOp (.cons 0)) []]
    let handlerCall := ClosLang.Exp.app .none none handlerSecond [.op .none (.blockOp (.elemAt 1)) [.var .none 1]]
    ClosSem.evaluate [closInterpreterBody] vars state =
      ClosSem.evaluate [.handle .none bodyCall handlerCall] vars state := by
  dsimp only
  let vars := [ClosSem.makeConst (.constCons 2 [body, handler]), ClosSem.Value.block 0 [], ClosSem.listToValue env]
  change ClosSem.evaluate [closInterpreterBody] vars state = _
  simp only [closInterpreterBody, interpreterIsCase_eq, interpreterVar_eq, interpreterGetEl_eq,
    interpreterCall_eq, interpreterCallList_eq, interpreterCons_eq, interpreterApp_eq]
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
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 2 2)) [.var .none 0]) _ _ vars state true (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.trueTag])]
  simp only [↓reduceIte]
  rfl

/-- A non-raised body result passes through the handler unchanged. -/
theorem interpreter_handle_nonraise {C F : Type} (source target targetFinal : ClosSem.State C F)
    (related : StateRel source target) (body handler : ClosLang.Const) (env : List ClosSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value) (clock : 3 ≤ target.clock)
    (notRaise : ∀ value, result ≠ .err (.raise value))
    (bodyRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst body, .block 0 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) =
      (result, targetFinal)) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons 2 [body, handler]), .block 0 [], ClosSem.listToValue env] target =
      (result, targetFinal) := by
  rw [interpreter_handle_entry body handler env target]
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  have call := evaluate_interpreter_field_call source target related 2 0 [body, handler] body (by simp)
    (.block 0 []) env false clock
  simp only [Bool.false_eq_true, ↓reduceIte] at call
  rw [call, bodyRun]
  cases result with
  | val values => rfl
  | err error =>
    cases error with
    | abort reason => rfl
    | raise value => exact (notRaise value rfl).elim

/-- A raised body value is prepended to the handler's environment. -/
theorem interpreter_handle_raise {C F : Type}
    (source sourceMid target targetMid targetFinal : ClosSem.State C F)
    (related : StateRel source target) (midRelated : StateRel sourceMid targetMid)
    (body handler : ClosLang.Const) (env : List ClosSem.Value) (value : ClosSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (clock : 3 ≤ target.clock) (midClock : 3 ≤ targetMid.clock)
    (bodyRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst body, .block 0 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) =
      (.err (.raise value), targetMid))
    (handlerRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst handler, .block 0 [], ClosSem.listToValue (value :: env)]
      (ClosSem.decClock 3 targetMid) = (result, targetFinal)) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons 2 [body, handler]), .block 0 [], ClosSem.listToValue env] target =
      (result, targetFinal) := by
  rw [interpreter_handle_entry body handler env target]
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  have call := evaluate_interpreter_field_call source target related 2 0 [body, handler] body (by simp)
    (.block 0 []) env false clock
  simp only [Bool.false_eq_true, ↓reduceIte] at call
  rw [call, bodyRun]
  let vars := [value, ClosSem.makeConst (.constCons 2 [body, handler]),
    ClosSem.Value.block 0 [], ClosSem.listToValue env]
  let extended := ClosLang.Exp.op .none (.blockOp (.cons 0)) [.var .none 3, .var .none 0]
  let flag := ClosLang.Exp.op .none (.blockOp (.cons 0)) []
  let code := ClosLang.Exp.op .none (.blockOp (.elemAt 1)) [.var .none 1]
  have environmentRun : ClosSem.evaluate [extended] vars targetMid =
      (.val [ClosSem.listToValue (value :: env)], targetMid) := by
    simp [extended, vars, ClosSem.listToValue, BackendCommon.consTag, ClosSem.evaluate,
      ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock]
  have flagRun : ClosSem.evaluate [flag] vars targetMid = (.val [.block 0 []], targetMid) := by
    simp [flag, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock]
  have codeRun : ClosSem.evaluate [code] vars targetMid = (.val [ClosSem.makeConst handler], targetMid) := by
    simp [code, vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock]
  have handlerCall := evaluate_interpreter_call sourceMid targetMid midRelated vars extended flag code
    (ClosSem.listToValue (value :: env)) (.block 0 []) (ClosSem.makeConst handler)
    environmentRun flagRun codeRun midClock
  change ClosSem.evaluate [.app .none none
    (.app .none none (.app .none none (.op .none (.globOp (.global 0)) []) [extended]) [flag]) [code]] vars targetMid = _
  rw [handlerCall, handlerRun]

/-- Handler case of the proof-side interpreter simulation. -/
theorem interpreter_correct_handle {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp)
    (bodyIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [body] env source = (result, sourceFinal) → canInterpret body = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant body), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (handlerIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [handler] env source = (result, sourceFinal) → canInterpret handler = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant handler), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.handle trace body handler] env source = (result, sourceFinal))
    (valid : canInterpret (.handle trace body handler) = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant (.handle trace body handler)), .block 0 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  have parts : canInterpret body = true ∧ canInterpret handler = true := by
    simpa [canInterpret, Bool.and_eq_true] using valid
  cases bodyRun : ClosSem.evaluate [body] env source with
  | mk bodyResult sourceMid =>
    have bodyNotTypeError : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bodyRun] at run
      simp at run
      exact notTypeError run.1.symm
    obtain ⟨bodyExtra, targetMid, targetBody, midRel⟩ :=
      bodyIH env source target sourceMid bodyResult bodyRun parts.1 assumption related bodyNotTypeError
    by_cases raises : ∃ value, bodyResult = .err (.raise value)
    · obtain ⟨value, rfl⟩ := raises
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bodyRun] at run
      have sourceBound : sourceMid.clock ≤ source.clock := by
        have bound := ClosSem.evaluate_clock_le [body] env source
        simpa [bodyRun] using bound
      obtain ⟨handlerExtra, targetFinal, targetHandler, finalRel⟩ :=
        handlerIH (value :: env) sourceMid targetMid sourceFinal result run parts.2
          (interpAssum_le assumption sourceBound) midRel notTypeError
      let offset := 3 + handlerExtra
      let enlarged := { target with clock := 3 + ((bodyExtra + target.clock) + offset) }
      let enlargedMid := { targetMid with clock := targetMid.clock + offset }
      have shiftedBody := ClosSem.evaluate_addClock.1 [closInterpreterBody]
        [ClosSem.makeConst (toConstant body), .block 0 [], ClosSem.listToValue env]
        { target with clock := bodyExtra + target.clock } targetMid (.err (.raise value))
        offset targetBody (by simp)
      have bodyRun' : ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant body), .block 0 [], ClosSem.listToValue env]
          (ClosSem.decClock 3 enlarged) = (.err (.raise value), enlargedMid) := by
        simpa [ClosSem.decClock, enlarged, enlargedMid] using shiftedBody
      have handlerRun' : ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant handler), .block 0 [], ClosSem.listToValue (value :: env)]
          (ClosSem.decClock 3 enlargedMid) = (result, targetFinal) := by
        have clocks : ClosSem.decClock 3 enlargedMid =
            { targetMid with clock := handlerExtra + targetMid.clock } := by
          simp only [ClosSem.decClock, enlargedMid, offset]
          congr 1
          omega
        rw [clocks]
        exact targetHandler
      have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged :=
        stateRel_withClock related enlarged.clock
      have enlargedMidRel : StateRel { sourceMid with clock := enlargedMid.clock } enlargedMid :=
        stateRel_withClock midRel enlargedMid.clock
      have enough : 3 ≤ enlarged.clock := by simp [enlarged]
      have midEnough : 3 ≤ enlargedMid.clock := by simp [enlargedMid, offset]; omega
      have reduction := interpreter_handle_raise { source with clock := enlarged.clock }
        { sourceMid with clock := enlargedMid.clock } enlarged enlargedMid targetFinal enlargedRel enlargedMidRel
        (toConstant body) (toConstant handler) env value result enough midEnough bodyRun' handlerRun'
      refine ⟨3 + (bodyExtra + offset), targetFinal, ?_, finalRel⟩
      simpa [toConstant, enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reduction
    · have notRaise : ∀ value, bodyResult ≠ .err (.raise value) := by
        intro value equal
        exact raises ⟨value, equal⟩
      have sourcePass : ClosSem.evaluate [.handle trace body handler] env source = (bodyResult, sourceMid) := by
        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bodyRun]
        cases bodyResult with
        | val values => rfl
        | err error =>
          cases error with
          | abort reason => rfl
          | raise value => exact (notRaise value rfl).elim
      rw [sourcePass] at run
      cases run
      let enlarged := { target with clock := 3 + (bodyExtra + target.clock) }
      have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged :=
        stateRel_withClock related enlarged.clock
      have enough : 3 ≤ enlarged.clock := by simp [enlarged]
      have clocks : ClosSem.decClock 3 enlarged = { target with clock := bodyExtra + target.clock } := by
        simp [ClosSem.decClock, enlarged]
      have targetRun' : ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant body), .block 0 [], ClosSem.listToValue env]
          (ClosSem.decClock 3 enlarged) = (result, targetMid) := by
        simpa only [clocks] using targetBody
      have reduction := interpreter_handle_nonraise { source with clock := enlarged.clock } enlarged targetMid
        enlargedRel (toConstant body) (toConstant handler) env result enough notRaise targetRun'
      refine ⟨3 + bodyExtra, targetMid, ?_, midRel⟩
      simpa [toConstant, enlarged, Nat.add_assoc] using reduction

end Flapjack.Compiler.Backend.ClosInterp
