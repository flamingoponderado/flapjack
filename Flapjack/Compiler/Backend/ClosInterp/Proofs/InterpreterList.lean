import Flapjack.Compiler.Backend.ClosInterp.Proofs.InterpreterTick
import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate

/-! Nonempty expression-list interpretation. Evaluator and state carriers
remain proof-side and await full HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- A nonempty encoded list selects the branch that interprets its head and
its tail and constructs the result list. -/
theorem interpreter_list_cons_entry {C F : Type} (head tail : ClosLang.Const) (env : List ClosSem.Value)
    (state : ClosSem.State C F) :
    let vars := [ClosSem.makeConst (.constCons 0 [head, tail]), .block 1 [], ClosSem.listToValue env]
    let global := ClosLang.Exp.op .none (.globOp (.global 0)) []
    let first := ClosLang.Exp.app .none none global [.var .none 2]
    let headCall := ClosLang.Exp.app .none none
      (.app .none none first [.op .none (.blockOp (.cons 0)) []])
      [.op .none (.blockOp (.elemAt 0)) [.var .none 0]]
    let tailCall := ClosLang.Exp.app .none none
      (.app .none none first [.op .none (.blockOp (.cons 1)) []])
      [.op .none (.blockOp (.elemAt 1)) [.var .none 0]]
    ClosSem.evaluate [closInterpreterBody] vars state =
      ClosSem.evaluate [.let .none [headCall, tailCall]
        (.op .none (.blockOp (.cons 0)) [.var .none 1, .var .none 0])] vars state := by
  dsimp only
  let vars := [ClosSem.makeConst (.constCons 0 [head, tail]), ClosSem.Value.block 1 [], ClosSem.listToValue env]
  change ClosSem.evaluate [closInterpreterBody] vars state = _
  simp only [closInterpreterBody, interpreterVar_eq, interpreterGetEl_eq, interpreterCons_eq,
    interpreterCall_eq, interpreterCallList_eq, interpreterApp_eq]
  rw [evaluate_if_condition (.var .none 1) _ _ vars state true (by
    simp [vars, ClosSem.evaluate, ClosSem.boolValue, BackendCommon.trueTag])]
  simp only [↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.lenEq 0)) [.var .none 0]) _ _ vars state false (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rfl


/-- If interpreting the head fails, the list interpreter propagates the
same error without evaluating the tail. -/
theorem interpreter_list_cons_head_error {C F : Type} (source target targetFinal : ClosSem.State C F)
    (related : StateRel source target) (head tail : ClosLang.Const) (env : List ClosSem.Value)
    (error : ErrorResult ClosSem.Value) (clock : 3 ≤ target.clock)
    (headRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst head, .block 0 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) =
      (.err error, targetFinal)) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons 0 [head, tail]), .block 1 [], ClosSem.listToValue env] target =
      (.err error, targetFinal) := by
  let vars := [ClosSem.makeConst (.constCons 0 [head, tail]), ClosSem.Value.block 1 [], ClosSem.listToValue env]
  let global := ClosLang.Exp.op .none (.globOp (.global 0)) []
  let first := ClosLang.Exp.app .none none global [.var .none 2]
  let headCall := ClosLang.Exp.app .none none
    (.app .none none first [.op .none (.blockOp (.cons 0)) []])
    [.op .none (.blockOp (.elemAt 0)) [.var .none 0]]
  let tailCall := ClosLang.Exp.app .none none
    (.app .none none first [.op .none (.blockOp (.cons 1)) []])
    [.op .none (.blockOp (.elemAt 1)) [.var .none 0]]
  have headCallRun : ClosSem.evaluate [headCall] vars target = (.err error, targetFinal) := by
    have reduction := evaluate_interpreter_field_call source target related 0 0 [head, tail] head (by simp)
      (.block 1 []) env false clock
    simpa [vars, headCall, first, global] using reduction.trans headRun
  have bindingsRun : ClosSem.evaluate [headCall, tailCall] vars target = (.err error, targetFinal) :=
    ClosProps.evaluate_cons_error headCall [tailCall] vars target targetFinal error headCallRun
  rw [interpreter_list_cons_entry head tail env target]
  change ClosSem.evaluate [.let .none [headCall, tailCall]
    (.op .none (.blockOp (.cons 0)) [.var .none 1, .var .none 0])] vars target = _
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bindingsRun]


/-- Once a head succeeds, the generated bindings interpret the tail in the
intermediate state and construct the encoded result list. -/
theorem interpreter_list_cons_success {C F : Type}
    (source sourceMid target targetMid targetFinal : ClosSem.State C F)
    (related : StateRel source target) (midRelated : StateRel sourceMid targetMid)
    (head tail : ClosLang.Const) (env : List ClosSem.Value) (value : ClosSem.Value)
    (values : List ClosSem.Value) (clock : 3 ≤ target.clock) (midClock : 3 ≤ targetMid.clock)
    (headRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst head, .block 0 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) =
      (.val [value], targetMid))
    (tailRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst tail, .block 1 [], ClosSem.listToValue env] (ClosSem.decClock 3 targetMid) =
      (.val [ClosSem.listToValue values], targetFinal)) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons 0 [head, tail]), .block 1 [], ClosSem.listToValue env] target =
      (.val [ClosSem.listToValue (value :: values)], targetFinal) := by
  let vars := [ClosSem.makeConst (.constCons 0 [head, tail]), ClosSem.Value.block 1 [], ClosSem.listToValue env]
  let global := ClosLang.Exp.op .none (.globOp (.global 0)) []
  let first := ClosLang.Exp.app .none none global [.var .none 2]
  let headCall := ClosLang.Exp.app .none none
    (.app .none none first [.op .none (.blockOp (.cons 0)) []])
    [.op .none (.blockOp (.elemAt 0)) [.var .none 0]]
  let tailCall := ClosLang.Exp.app .none none
    (.app .none none first [.op .none (.blockOp (.cons 1)) []])
    [.op .none (.blockOp (.elemAt 1)) [.var .none 0]]
  have headCallRun : ClosSem.evaluate [headCall] vars target = (.val [value], targetMid) := by
    have reduction := evaluate_interpreter_field_call source target related 0 0 [head, tail] head (by simp)
      (.block 1 []) env false clock
    simpa [vars, headCall, first, global] using reduction.trans headRun
  have tailCallRun : ClosSem.evaluate [tailCall] vars targetMid = (.val [ClosSem.listToValue values], targetFinal) := by
    have reduction := evaluate_interpreter_field_call sourceMid targetMid midRelated 0 1 [head, tail] tail (by simp)
      (.block 1 []) env true midClock
    simpa [vars, tailCall, first, global] using reduction.trans tailRun
  have bindingsRun : ClosSem.evaluate [headCall, tailCall] vars target =
      (.val [value, ClosSem.listToValue values], targetFinal) := by
    rw [ClosProps.evaluate_cons_value headCall [tailCall] vars target targetMid value headCallRun, tailCallRun]
  rw [interpreter_list_cons_entry head tail env target]
  change ClosSem.evaluate [.let .none [headCall, tailCall]
    (.op .none (.blockOp (.cons 0)) [.var .none 1, .var .none 0])] vars target = _
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bindingsRun]
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
    ClosSem.listToValue, BackendCommon.consTag]


/-- If the head succeeds and the tail fails, the list interpreter
propagates the tail error. -/
theorem interpreter_list_cons_tail_error {C F : Type}
    (source sourceMid target targetMid targetFinal : ClosSem.State C F)
    (related : StateRel source target) (midRelated : StateRel sourceMid targetMid)
    (head tail : ClosLang.Const) (env : List ClosSem.Value) (value : ClosSem.Value)
    (error : ErrorResult ClosSem.Value) (clock : 3 ≤ target.clock) (midClock : 3 ≤ targetMid.clock)
    (headRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst head, .block 0 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) =
      (.val [value], targetMid))
    (tailRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst tail, .block 1 [], ClosSem.listToValue env] (ClosSem.decClock 3 targetMid) =
      (.err error, targetFinal)) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons 0 [head, tail]), .block 1 [], ClosSem.listToValue env] target =
      (.err error, targetFinal) := by
  let vars := [ClosSem.makeConst (.constCons 0 [head, tail]), ClosSem.Value.block 1 [], ClosSem.listToValue env]
  let global := ClosLang.Exp.op .none (.globOp (.global 0)) []
  let first := ClosLang.Exp.app .none none global [.var .none 2]
  let headCall := ClosLang.Exp.app .none none
    (.app .none none first [.op .none (.blockOp (.cons 0)) []])
    [.op .none (.blockOp (.elemAt 0)) [.var .none 0]]
  let tailCall := ClosLang.Exp.app .none none
    (.app .none none first [.op .none (.blockOp (.cons 1)) []])
    [.op .none (.blockOp (.elemAt 1)) [.var .none 0]]
  have headCallRun : ClosSem.evaluate [headCall] vars target = (.val [value], targetMid) := by
    have reduction := evaluate_interpreter_field_call source target related 0 0 [head, tail] head (by simp)
      (.block 1 []) env false clock
    simpa [vars, headCall, first, global] using reduction.trans headRun
  have tailCallRun : ClosSem.evaluate [tailCall] vars targetMid = (.err error, targetFinal) := by
    have reduction := evaluate_interpreter_field_call sourceMid targetMid midRelated 0 1 [head, tail] tail (by simp)
      (.block 1 []) env true midClock
    simpa [vars, tailCall, first, global] using reduction.trans tailRun
  have bindingsRun : ClosSem.evaluate [headCall, tailCall] vars target =
      (.err error, targetFinal) := by
    rw [ClosProps.evaluate_cons_value headCall [tailCall] vars target targetMid value headCallRun, tailCallRun]
  rw [interpreter_list_cons_entry head tail env target]
  change ClosSem.evaluate [.let .none [headCall, tailCall]
    (.op .none (.blockOp (.cons 0)) [.var .none 1, .var .none 0])] vars target = _
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bindingsRun]



/-- Nonempty-list simulation when the source head raises an error. The
head evaluation identifies this control-flow case of the list induction. -/
theorem interpreter_correct_list_cons_head_error {C F : Type}
    (head : ClosLang.Exp) (tail : List ClosLang.Exp)
    (ih : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [head] env source = (result, sourceFinal) → canInterpret head = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant head), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (error : ErrorResult ClosSem.Value)
    (headRun : ClosSem.evaluate [head] env source = (.err error, sourceFinal))
    (valid : canInterpretList (head :: tail) = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : Result.err error ≠ (Result.err (.abort .typeError) : Result (List ClosSem.Value) ClosSem.Value)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstantList (head :: tail)), .block 1 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (.err error, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  have headValid : canInterpret head = true := by
    have both : canInterpret head = true ∧ canInterpretList tail = true := by
      simpa [canInterpretList] using valid
    exact both.1
  obtain ⟨extra, targetFinal, targetRun, finalRel⟩ :=
    ih env source target sourceFinal (.err error) headRun headValid assumption related notTypeError
  let enlarged := { target with clock := 3 + (extra + target.clock) }
  have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged :=
    stateRel_withClock related enlarged.clock
  have enough : 3 ≤ enlarged.clock := by simp [enlarged]
  have clocks : ClosSem.decClock 3 enlarged = { target with clock := extra + target.clock } := by
    simp [ClosSem.decClock, enlarged]
  have headRun' : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstant head), .block 0 [], ClosSem.listToValue env]
      (ClosSem.decClock 3 enlarged) = (.err error, targetFinal) := by
    simpa only [clocks] using targetRun
  have reduction := interpreter_list_cons_head_error { source with clock := enlarged.clock } enlarged targetFinal
    enlargedRel (toConstant head) (toConstantList tail) env error enough headRun'
  refine ⟨3 + extra, targetFinal, ?_, finalRel⟩
  simpa [toConstantList, enlarged, Nat.add_assoc] using reduction

end Flapjack.Compiler.Backend.ClosInterp
