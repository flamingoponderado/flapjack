import Flapjack.Compiler.Backend.ClosInterp.Proofs.InterpreterTick
import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength

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

/-- A successful head and tail compose into the successful nonempty-list
simulation. The head run may be extended to provide the tail's clock. -/
theorem interpreter_correct_list_cons_success {C F : Type}
    (head : ClosLang.Exp) (tail : List ClosLang.Exp)
    (headIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [head] env source = (result, sourceFinal) → canInterpret head = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant head), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (tailIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (values : List ClosSem.Value),
      ClosSem.evaluate tail env source = (.val values, sourceFinal) → canInterpretList tail = true →
      InterpAssum C F source.clock → StateRel source target →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstantList tail), .block 1 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (.val [ClosSem.listToValue values], targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source sourceMid sourceFinal target : ClosSem.State C F)
    (value : ClosSem.Value) (values : List ClosSem.Value)
    (headRun : ClosSem.evaluate [head] env source = (.val [value], sourceMid))
    (tailRun : ClosSem.evaluate tail env sourceMid = (.val values, sourceFinal))
    (valid : canInterpretList (head :: tail) = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstantList (head :: tail)), .block 1 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (.val [ClosSem.listToValue (value :: values)], targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  have validParts : canInterpret head = true ∧ canInterpretList tail = true := by
    simpa [canInterpretList] using valid
  obtain ⟨headExtra, targetMid, targetHead, midRel⟩ :=
    headIH env source target sourceMid (.val [value]) headRun validParts.1 assumption related (by simp)
  have sourceBound : sourceMid.clock ≤ source.clock := by
    have bound := ClosSem.evaluate_clock_le [head] env source
    simpa [headRun] using bound
  obtain ⟨tailExtra, targetFinal, targetTail, finalRel⟩ :=
    tailIH env sourceMid targetMid sourceFinal values tailRun validParts.2
      (interpAssum_le assumption sourceBound) midRel
  let offset := 3 + tailExtra
  let enlarged := { target with clock := 3 + ((headExtra + target.clock) + offset) }
  let enlargedMid := { targetMid with clock := targetMid.clock + offset }
  have shiftedHead := ClosSem.evaluate_addClock.1 [closInterpreterBody]
    [ClosSem.makeConst (toConstant head), .block 0 [], ClosSem.listToValue env]
    { target with clock := headExtra + target.clock } targetMid (.val [value]) offset targetHead (by simp)
  have headRun' : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstant head), .block 0 [], ClosSem.listToValue env]
      (ClosSem.decClock 3 enlarged) = (.val [value], enlargedMid) := by
    simpa [ClosSem.decClock, enlarged, enlargedMid] using shiftedHead
  have tailRun' : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstantList tail), .block 1 [], ClosSem.listToValue env]
      (ClosSem.decClock 3 enlargedMid) = (.val [ClosSem.listToValue values], targetFinal) := by
    have clocks : ClosSem.decClock 3 enlargedMid =
        { targetMid with clock := tailExtra + targetMid.clock } := by
      simp only [ClosSem.decClock, enlargedMid, offset]
      congr 1
      omega
    rw [clocks]
    exact targetTail
  have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged :=
    stateRel_withClock related enlarged.clock
  have enlargedMidRel : StateRel { sourceMid with clock := enlargedMid.clock } enlargedMid :=
    stateRel_withClock midRel enlargedMid.clock
  have enough : 3 ≤ enlarged.clock := by simp [enlarged]
  have midEnough : 3 ≤ enlargedMid.clock := by simp [enlargedMid, offset]; omega
  have reduction := interpreter_list_cons_success { source with clock := enlarged.clock }
    { sourceMid with clock := enlargedMid.clock } enlarged enlargedMid targetFinal enlargedRel enlargedMidRel
    (toConstant head) (toConstantList tail) env value values enough midEnough headRun' tailRun'
  refine ⟨3 + (headExtra + offset), targetFinal, ?_, finalRel⟩
  simpa [toConstantList, enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reduction

theorem interpreter_correct_list_success {C F : Type}
    (head : ClosLang.Exp) (tail : List ClosLang.Exp)
    (headIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [head] env source = (result, sourceFinal) → canInterpret head = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant head), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (tailIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (values : List ClosSem.Value),
      ClosSem.evaluate tail env source = (.val values, sourceFinal) → canInterpretList tail = true →
      InterpAssum C F source.clock → StateRel source target →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstantList tail), .block 1 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (.val [ClosSem.listToValue values], targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (values : List ClosSem.Value)
    (run : ClosSem.evaluate (head :: tail) env source = (.val values, sourceFinal))
    (valid : canInterpretList (head :: tail) = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstantList (head :: tail)), .block 1 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (.val [ClosSem.listToValue values], targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  cases headRun : ClosSem.evaluate [head] env source with
  | mk result sourceMid =>
    cases result with
    | err error =>
      have failed := ClosProps.evaluate_cons_error head tail env source sourceMid error headRun
      rw [failed] at run
      simp at run
    | val headValues =>
      obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value head env source sourceMid headValues headRun
      cases tailRun : ClosSem.evaluate tail env sourceMid with
      | mk tailResult last =>
        have sequence := ClosProps.evaluate_cons_value head tail env source sourceMid value headRun
        rw [sequence, tailRun] at run
        cases tailResult with
        | err error => simp at run
        | val tailValues =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact interpreter_correct_list_cons_success head tail headIH tailIH env source sourceMid last target
            value tailValues headRun tailRun valid assumption related

/-- The tail-error case composes both induction hypotheses after a successful head. -/
theorem interpreter_correct_list_cons_tail_error {C F : Type}
    (head : ClosLang.Exp) (tail : List ClosLang.Exp)
    (headIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [head] env source = (result, sourceFinal) → canInterpret head = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant head), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (tailIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (error : ErrorResult ClosSem.Value),
      ClosSem.evaluate tail env source = (.err error, sourceFinal) → canInterpretList tail = true →
      InterpAssum C F source.clock → StateRel source target →
      (Result.err error : Result (List ClosSem.Value) ClosSem.Value) ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstantList tail), .block 1 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (.err error, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source sourceMid sourceFinal target : ClosSem.State C F)
    (value : ClosSem.Value) (error : ErrorResult ClosSem.Value)
    (headRun : ClosSem.evaluate [head] env source = (.val [value], sourceMid))
    (tailRun : ClosSem.evaluate tail env sourceMid = (.err error, sourceFinal))
    (valid : canInterpretList (head :: tail) = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : (Result.err error : Result (List ClosSem.Value) ClosSem.Value) ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstantList (head :: tail)), .block 1 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (.err error, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  have validParts : canInterpret head = true ∧ canInterpretList tail = true := by
    simpa [canInterpretList] using valid
  obtain ⟨headExtra, targetMid, targetHead, midRel⟩ :=
    headIH env source target sourceMid (.val [value]) headRun validParts.1 assumption related (by simp)
  have sourceBound : sourceMid.clock ≤ source.clock := by
    have bound := ClosSem.evaluate_clock_le [head] env source
    simpa [headRun] using bound
  obtain ⟨tailExtra, targetFinal, targetTail, finalRel⟩ :=
    tailIH env sourceMid targetMid sourceFinal error tailRun validParts.2
      (interpAssum_le assumption sourceBound) midRel notTypeError
  let offset := 3 + tailExtra
  let enlarged := { target with clock := 3 + ((headExtra + target.clock) + offset) }
  let enlargedMid := { targetMid with clock := targetMid.clock + offset }
  have shiftedHead := ClosSem.evaluate_addClock.1 [closInterpreterBody]
    [ClosSem.makeConst (toConstant head), .block 0 [], ClosSem.listToValue env]
    { target with clock := headExtra + target.clock } targetMid (.val [value]) offset targetHead (by simp)
  have headRun' : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstant head), .block 0 [], ClosSem.listToValue env]
      (ClosSem.decClock 3 enlarged) = (.val [value], enlargedMid) := by
    simpa [ClosSem.decClock, enlarged, enlargedMid] using shiftedHead
  have tailRun' : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstantList tail), .block 1 [], ClosSem.listToValue env]
      (ClosSem.decClock 3 enlargedMid) = (.err error, targetFinal) := by
    have clocks : ClosSem.decClock 3 enlargedMid =
        { targetMid with clock := tailExtra + targetMid.clock } := by
      simp only [ClosSem.decClock, enlargedMid, offset]
      congr 1
      omega
    rw [clocks]
    exact targetTail
  have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged :=
    stateRel_withClock related enlarged.clock
  have enlargedMidRel : StateRel { sourceMid with clock := enlargedMid.clock } enlargedMid :=
    stateRel_withClock midRel enlargedMid.clock
  have enough : 3 ≤ enlarged.clock := by simp [enlarged]
  have midEnough : 3 ≤ enlargedMid.clock := by simp [enlargedMid, offset]; omega
  have reduction := interpreter_list_cons_tail_error { source with clock := enlarged.clock }
    { sourceMid with clock := enlargedMid.clock } enlarged enlargedMid targetFinal enlargedRel enlargedMidRel
    (toConstant head) (toConstantList tail) env value error enough midEnough headRun' tailRun'
  refine ⟨3 + (headExtra + offset), targetFinal, ?_, finalRel⟩
  simpa [toConstantList, enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reduction

/-- Inductive nonempty-list simulation for all non-type-error results. -/
theorem interpreter_correct_list_cons {C F : Type}
    (head : ClosLang.Exp) (tail : List ClosLang.Exp)
    (headIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [head] env source = (result, sourceFinal) → canInterpret head = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant head), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (tailIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate tail env source = (result, sourceFinal) → canInterpretList tail = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstantList tail), .block 1 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } =
            (match result with
             | .err error => .err error
             | .val values => .val [ClosSem.listToValue values], targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate (head :: tail) env source = (result, sourceFinal))
    (valid : canInterpretList (head :: tail) = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstantList (head :: tail)), .block 1 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } =
          (match result with
           | .err error => .err error
           | .val values => .val [ClosSem.listToValue values], targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  cases result with
  | val values =>
    apply interpreter_correct_list_success head tail headIH ?_ env source target sourceFinal values run valid assumption related
    intro env source target sourceFinal values run valid assumption related
    exact tailIH env source target sourceFinal (.val values) run valid assumption related (by simp)
  | err error =>
    cases headRun : ClosSem.evaluate [head] env source with
    | mk headResult sourceMid =>
      cases headResult with
      | err headError =>
        have failed := ClosProps.evaluate_cons_error head tail env source sourceMid headError headRun
        rw [failed] at run
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact interpreter_correct_list_cons_head_error head tail headIH env source target sourceMid headError
          headRun valid assumption related notTypeError
      | val headValues =>
        obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value head env source sourceMid headValues headRun
        cases tailRun : ClosSem.evaluate tail env sourceMid with
        | mk tailResult last =>
          have sequence := ClosProps.evaluate_cons_value head tail env source sourceMid value headRun
          rw [sequence, tailRun] at run
          cases tailResult with
          | val values => simp at run
          | err tailError =>
            simp at run
            rcases run with ⟨rfl, rfl⟩
            apply interpreter_correct_list_cons_tail_error head tail headIH ?_ env source sourceMid last target
              value tailError headRun tailRun valid assumption related notTypeError
            intro env source target sourceFinal error run valid assumption related notTypeError
            exact tailIH env source target sourceFinal (.err error) run valid assumption related notTypeError

/-- List simulation assembled from the expression simulations for its members. -/
theorem interpreter_correct_list_of_members {C F : Type} (expressions : List ClosLang.Exp)
    (memberIH : ∀ head ∈ expressions, ∀ (env : List ClosSem.Value)
      (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [head] env source = (result, sourceFinal) → canInterpret head = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant head), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate expressions env source = (result, sourceFinal))
    (valid : canInterpretList expressions = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstantList expressions), .block 1 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } =
          (match result with
           | .err error => .err error
           | .val values => .val [ClosSem.listToValue values], targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  induction expressions generalizing env source target sourceFinal result with
  | nil =>
    simp only [ClosSem.evaluate] at run
    cases run
    refine ⟨0, target, ?_, related⟩
    simpa using interpreter_list_nil env target
  | cons head tail ih =>
    cases result <;>
      apply interpreter_correct_list_cons head tail (memberIH head (by simp)) ?_
        env source target sourceFinal _ run valid assumption related notTypeError <;>
      intro tailEnv tailSource tailTarget tailFinal tailResult tailRun tailValid tailAssumption tailRelated tailNotTypeError <;>
      cases tailResult <;>
      apply ih ?_ tailEnv tailSource tailTarget tailFinal _ tailRun tailValid tailAssumption tailRelated tailNotTypeError <;>
      intro expression member <;>
      exact memberIH expression (by simp [member])

end Flapjack.Compiler.Backend.ClosInterp
