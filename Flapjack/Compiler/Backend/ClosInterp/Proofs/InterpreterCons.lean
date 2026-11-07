import Flapjack.Compiler.Backend.ClosInterp.Proofs.InterpreterApp

/-! Constructor-operation simulation for the proof-side interpreter. Its
semantics and state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- Nonempty constructor encodings select argument interpretation and reversal. -/
theorem interpreter_cons_entry {C F : Type} (tag : Nat) (args : ClosLang.Const)
    (env : List ClosSem.Value) (state : ClosSem.State C F) :
    let vars := [ClosSem.makeConst (.constCons (tag + 5) [args]), .block 0 [], ClosSem.listToValue env]
    let global := ClosLang.Exp.op .none (.globOp (.global 0)) []
    let first := ClosLang.Exp.app .none none global [.var .none 2]
    let second := ClosLang.Exp.app .none none first [.op .none (.blockOp (.cons 1)) []]
    let call := ClosLang.Exp.app .none none second [.op .none (.blockOp (.elemAt 0)) [.var .none 0]]
    let reverseCall := ClosLang.Exp.app .none none (.app .none none (.var .none 0) [.var .none 1])
      [.op .none (.blockOp (.cons 0)) []]
    let mkCase := fun n yes no => ClosLang.Exp.ifThenElse .none
      (.op .none (.blockOp (.tagLenEq n 1)) [.var .none 0]) yes no
    let fromList := fun n => ClosLang.Exp.op .none (.blockOp (.fromList n)) [.var .none 1]
    let dispatch := mkCase 5 (fromList 0) (mkCase 6 (fromList 1) (mkCase 7 (fromList 2)
      (.op .none (.blockOp (.cons 0)) [])))
    let continuation := ClosLang.Exp.letrec [] none none
      [(1, .fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpRev)]
      (.let .none [reverseCall] (.let .none [.var .none 3] dispatch))
    ClosSem.evaluate [closInterpreterBody] vars state =
      ClosSem.evaluate [.let .none [call] continuation] vars state := by
  dsimp only
  let vars := [ClosSem.makeConst (.constCons (tag + 5) [args]), ClosSem.Value.block 0 [], ClosSem.listToValue env]
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
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 2 2)) [.var .none 0]) _ _ vars state false (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 0 3)) [.var .none 0]) _ _ vars state false (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 3 1)) [.var .none 0]) _ _ vars state false (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 4 1)) [.var .none 0]) _ _ vars state false (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rfl

/-- An error in the constructor fields prevents reversal and construction. -/
theorem interpreter_cons_arguments_error {C F : Type} (source target targetFinal : ClosSem.State C F)
    (related : StateRel source target) (tag : Nat) (args : ClosLang.Const) (env : List ClosSem.Value)
    (error : ErrorResult ClosSem.Value) (clock : 3 ≤ target.clock)
    (argsRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst args, .block 1 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) =
      (.err error, targetFinal)) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons (tag + 5) [args]), .block 0 [], ClosSem.listToValue env] target =
      (.err error, targetFinal) := by
  rw [interpreter_cons_entry tag args env target]
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  have call := evaluate_interpreter_field_call source target related (tag + 5) 0 [args] args (by simp)
    (.block 0 []) env true clock
  simp only [↓reduceIte] at call
  rw [call, argsRun]

/-- Reversing the interpreted fields restores constructor order. -/
theorem interpreter_cons_continuation {C F : Type} (tag : Nat) (args : ClosLang.Const)
    (env values : List ClosSem.Value) (state : ClosSem.State C F)
    (positive : 1 ≤ state.maxApp) (supported : tag < 3) :
    let vars := [ClosSem.listToValue values, ClosSem.makeConst (.constCons (tag + 5) [args]),
      ClosSem.Value.block 0 [], ClosSem.listToValue env]
    let reverseCall := ClosLang.Exp.app .none none (.app .none none (.var .none 0) [.var .none 1])
      [.op .none (.blockOp (.cons 0)) []]
    let mkCase := fun n yes no => ClosLang.Exp.ifThenElse .none
      (.op .none (.blockOp (.tagLenEq n 1)) [.var .none 0]) yes no
    let fromList := fun n => ClosLang.Exp.op .none (.blockOp (.fromList n)) [.var .none 1]
    let dispatch := mkCase 5 (fromList 0) (mkCase 6 (fromList 1) (mkCase 7 (fromList 2)
      (.op .none (.blockOp (.cons 0)) [])))
    let continuation := ClosLang.Exp.letrec [] none none
      [(1, .fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpRev)]
      (.let .none [reverseCall] (.let .none [.var .none 3] dispatch))
    ClosSem.evaluate [continuation] vars { state with clock := (2 * values.length + 2) + state.clock } =
      (.val [.block tag values.reverse], state) := by
  dsimp only
  rw [ClosSem.evaluate.eq_def]
  simp only [List.all_cons, List.all_nil, Bool.and_true, positive, decide_true]
  simp only [Bool.true_and, (show ((1 : Nat) != 0) = true by decide), ↓reduceIte]
  let captured := [ClosSem.listToValue values, ClosSem.makeConst (.constCons (tag + 5) [args]),
    ClosSem.Value.block 0 [], ClosSem.listToValue env]
  let recFun := ClosSem.Value.recclosure none [] captured
    [(1, .fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpRev)] 0
  let workEnv := recFun :: captured
  let start := { state with clock := (2 * values.length + 2) + state.clock }
  let inner := ClosLang.Exp.app .none none (.var .none 0) [.var .none 1]
  let empty := ClosLang.Exp.op .none (.blockOp (.cons 0)) []
  let closure := ClosSem.Value.closure none [] (ClosSem.listToValue values :: recFun :: captured) 1 closInterpRev
  have argumentRun : ClosSem.evaluate [.var .none 1] workEnv start = (.val [ClosSem.listToValue values], start) := by
    simp [workEnv, captured, ClosSem.evaluate]
  have functionRun : ClosSem.evaluate [.var .none 0] workEnv start = (.val [recFun], start) := by
    simp [workEnv, ClosSem.evaluate]
  have recCall : ClosSem.destClosure start.maxApp none recFun [ClosSem.listToValue values] =
      some (.fullApp (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpRev)
        (ClosSem.listToValue values :: recFun :: captured) []) := by
    simp [recFun, ClosSem.destClosure, ClosSem.checkLoc, start, positive]
  have innerRun : ClosSem.evaluate [inner] workEnv start = (.val [closure], ClosSem.decClock 1 start) := by
    rw [show ClosSem.evaluate [inner] workEnv start = ClosSem.evaluateApp none recFun [ClosSem.listToValue values] start from
      evaluate_unary_app _ _ _ _ _ _ _ _ argumentRun functionRun]
    rw [FlatToClos.evaluateApp_unary _ _ _ _ _ recCall]
    simp [ClosSem.evaluate, ClosSem.decClock, start, positive, closure]
  have emptyRun : ClosSem.evaluate [empty] workEnv start = (.val [ClosSem.listToValue []], start) := by
    simp [empty, ClosSem.listToValue, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock, BackendCommon.nilTag]
  have closureCall : ClosSem.destClosure (ClosSem.decClock 1 start).maxApp none closure [ClosSem.listToValue []] =
      some (.fullApp closInterpRev (ClosSem.listToValue [] :: ClosSem.listToValue values :: recFun :: captured) []) := by
    simp [closure, ClosSem.destClosure, ClosSem.checkLoc, ClosSem.decClock, start, positive]
  have reverseRun : ClosSem.evaluate [.app .none none inner [empty]] workEnv start =
      (.val [ClosSem.listToValue values.reverse], state) := by
    rw [evaluate_unary_app inner empty workEnv start start (ClosSem.decClock 1 start)
      (ClosSem.listToValue []) closure emptyRun innerRun]
    rw [FlatToClos.evaluateApp_unary _ _ _ _ _ closureCall]
    have nonzero : (ClosSem.decClock 1 start).clock ≠ 0 := by simp [ClosSem.decClock, start]
    have clocks : ClosSem.decClock 1 (ClosSem.decClock 1 start) =
        { state with clock := 2 * values.length + state.clock } := by
      simp only [ClosSem.decClock, start]
      congr 1
      omega
    simp only [nonzero, ↓reduceIte, clocks]
    simpa [recFun] using evaluate_closInterpRev values [] captured captured state positive
  change ClosSem.evaluate [.let .none [.app .none none inner [empty]] _] workEnv start = _
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, reverseRun]
  have tags : tag = 0 ∨ tag = 1 ∨ tag = 2 := by omega
  rcases tags with rfl | rfl | rfl <;>
    simp [workEnv, captured, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp,
      ClosSem.applyBlock, ClosSem.asBool, ClosSem.boolValue, BackendCommon.trueTag, BackendCommon.falseTag,
      ClosSem.valueToList_listToValue]

/-- Successful constructor fields are reversed and assembled into the block. -/
theorem interpreter_cons_arguments_value {C F : Type}
    (source sourceMid target targetMid : ClosSem.State C F)
    (related : StateRel source target) (midRelated : StateRel sourceMid targetMid)
    (tag : Nat) (args : ClosLang.Const) (env values : List ClosSem.Value)
    (clock : 3 ≤ target.clock) (supported : tag < 3)
    (argsRun : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst args, .block 1 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) =
      (.val [ClosSem.listToValue values],
        { targetMid with clock := (2 * values.length + 2) + targetMid.clock })) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons (tag + 5) [args]), .block 0 [], ClosSem.listToValue env] target =
      (.val [.block tag values.reverse], targetMid) := by
  rw [interpreter_cons_entry tag args env target]
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  have call := evaluate_interpreter_field_call source target related (tag + 5) 0 [args] args (by simp)
    (.block 0 []) env true clock
  simp only [↓reduceIte] at call
  rw [call, argsRun]
  have positive : 1 ≤ targetMid.maxApp := by
    rcases midRelated.1 with ⟨_, _, _, maxEq, maxPositive, _⟩
    omega
  exact interpreter_cons_continuation tag args env values targetMid positive supported

/-- Nonempty supported constructor case of the interpreter simulation. -/
theorem interpreter_correct_cons_nonempty {C F : Type} (trace : BackendCommon.Tra)
    (tag : Nat) (args : List ClosLang.Exp) (nonempty : args ≠ []) (supported : tag < 3)
    (argsIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env source = (result, sourceFinal) → canInterpretList args = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstantList args), .block 1 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } =
          (match result with
           | .err error => .err error
           | .val values => .val [ClosSem.listToValue values], targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.op trace (.blockOp (.cons tag)) args] env source = (result, sourceFinal))
    (valid : canInterpretList args = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant (.op trace (.blockOp (.cons tag)) args)), .block 0 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  rw [ClosSem.evaluate_ordinaryOp_eq trace (.blockOp (.cons tag)) args env source (by simp) (by simp)] at run
  cases argsRun : ClosSem.evaluate args env source with
  | mk argsResult sourceMid =>
    rw [argsRun] at run
    cases argsResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨extra, targetFinal, targetRun, finalRel⟩ :=
        argsIH env source target sourceMid (.err error) argsRun valid assumption related notTypeError
      let enlarged := { target with clock := 3 + (extra + target.clock) }
      have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged :=
        stateRel_withClock related enlarged.clock
      have enough : 3 ≤ enlarged.clock := by simp [enlarged]
      have clocks : ClosSem.decClock 3 enlarged = { target with clock := extra + target.clock } := by
        simp [ClosSem.decClock, enlarged]
      have targetRun' : ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstantList args), .block 1 [], ClosSem.listToValue env]
          (ClosSem.decClock 3 enlarged) = (.err error, targetFinal) := by
        simpa only [clocks] using targetRun
      have reduction := interpreter_cons_arguments_error { source with clock := enlarged.clock } enlarged targetFinal
        enlargedRel tag (toConstantList args) env error enough targetRun'
      refine ⟨3 + extra, targetFinal, ?_, finalRel⟩
      have lengthNe : args.length ≠ 0 := by
        cases args with
        | nil => exact (nonempty rfl).elim
        | cons head tail => simp
      simpa [toConstant, toConstantOp, lengthNe, enlarged, Nat.add_assoc] using reduction
    | val values =>
      simp [ClosSem.doApp, ClosSem.applyBlock] at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨extra, targetMid, targetRun, midRel⟩ :=
        argsIH env source target sourceMid (.val values) argsRun valid assumption related (by simp)
      let cost := 2 * values.length + 2
      let enlarged := { target with clock := 3 + ((extra + target.clock) + cost) }
      have shifted := ClosSem.evaluate_addClock.1 [closInterpreterBody]
        [ClosSem.makeConst (toConstantList args), .block 1 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } targetMid (.val [ClosSem.listToValue values])
        cost targetRun (by simp)
      have targetRun' : ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstantList args), .block 1 [], ClosSem.listToValue env]
          (ClosSem.decClock 3 enlarged) =
          (.val [ClosSem.listToValue values], { targetMid with clock := cost + targetMid.clock }) := by
        simpa [ClosSem.decClock, enlarged, Nat.add_comm] using shifted
      have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged :=
        stateRel_withClock related enlarged.clock
      have enough : 3 ≤ enlarged.clock := by simp [enlarged]
      have reduction := interpreter_cons_arguments_value { source with clock := enlarged.clock } sourceMid
        enlarged targetMid enlargedRel midRel tag (toConstantList args) env values enough supported (by
          simpa [cost] using targetRun')
      refine ⟨3 + (extra + cost), targetMid, ?_, midRel⟩
      have lengthNe : args.length ≠ 0 := by
        cases args with
        | nil => exact (nonempty rfl).elim
        | cons head tail => simp
      simpa [toConstant, toConstantOp, lengthNe, enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reduction

/-- Constructor case for the subset accepted by `canInterpret`. -/
theorem interpreter_correct_cons {C F : Type} (trace : BackendCommon.Tra)
    (tag : Nat) (args : List ClosLang.Exp)
    (argsIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env source = (result, sourceFinal) → canInterpretList args = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstantList args), .block 1 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } =
          (match result with
           | .err error => .err error
           | .val values => .val [ClosSem.listToValue values], targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.op trace (.blockOp (.cons tag)) args] env source = (result, sourceFinal))
    (valid : canInterpret (.op trace (.blockOp (.cons tag)) args) = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant (.op trace (.blockOp (.cons tag)) args)), .block 0 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  cases args with
  | nil =>
    exact interpreter_correct_nullary_constructor trace tag env source target sourceFinal result run valid assumption related notTypeError
  | cons head tail =>
    have parts : tag < 3 ∧ canInterpretList (head :: tail) = true := by
      simpa [canInterpret, canInterpretOp, Bool.and_eq_true] using valid
    exact interpreter_correct_cons_nonempty trace tag (head :: tail) (by simp) parts.1 argsIH
      env source target sourceFinal result run parts.2 assumption related notTypeError

/-- Operator case for the subset accepted by `canInterpret`. -/
theorem interpreter_correct_op {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp)
    (argsIH : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env source = (result, sourceFinal) → canInterpretList args = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstantList args), .block 1 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } =
          (match result with
           | .err error => .err error
           | .val values => .val [ClosSem.listToValue values], targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.op trace op args] env source = (result, sourceFinal))
    (valid : canInterpret (.op trace op args) = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant (.op trace op args)), .block 0 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  cases op with
  | intOp operation =>
    cases operation with
    | const number =>
      cases args with
      | nil => exact interpreter_correct_integer_constant trace number env source target sourceFinal result run valid assumption related notTypeError
      | cons head tail => simp [canInterpret, canInterpretOp] at valid
    | _ => simp [canInterpret, canInterpretOp] at valid
  | globOp operation =>
    cases operation with
    | global index =>
      cases args with
      | nil => exact interpreter_correct_global trace index env source target sourceFinal result run valid assumption related notTypeError
      | cons head tail => simp [canInterpret, canInterpretOp] at valid
    | _ => simp [canInterpret, canInterpretOp] at valid
  | blockOp operation =>
    cases operation with
    | cons tag => exact interpreter_correct_cons trace tag args argsIH env source target sourceFinal result run valid assumption related notTypeError
    | constant constant =>
      cases args with
      | nil => exact interpreter_correct_block_constant trace constant env source target sourceFinal result run valid assumption related notTypeError
      | cons head tail => simp [canInterpret, canInterpretOp] at valid
    | _ => simp [canInterpret, canInterpretOp] at valid
  | _ => simp [canInterpret, canInterpretOp] at valid

end Flapjack.Compiler.Backend.ClosInterp
