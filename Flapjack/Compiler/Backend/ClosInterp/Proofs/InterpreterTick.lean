import Flapjack.Compiler.Backend.ClosInterp.Proofs.InterpreterRaise

/-! The interpreter's tick-expression dispatch. Its evaluator and state
carriers remain proof-side and await HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- A tick encoding selects the branch that recursively interprets its
single encoded child. -/
theorem interpreter_tick_entry {C F : Type} (child : ClosLang.Const) (env : List ClosSem.Value)
    (state : ClosSem.State C F) :
    let vars := [ClosSem.makeConst (.constCons 4 [child]), .block 0 [], ClosSem.listToValue env]
    let global := ClosLang.Exp.op .none (.globOp (.global 0)) []
    let first := ClosLang.Exp.app .none none global [.var .none 2]
    let second := ClosLang.Exp.app .none none first [.op .none (.blockOp (.cons 0)) []]
    ClosSem.evaluate [closInterpreterBody] vars state =
      ClosSem.evaluate [.app .none none second [.op .none (.blockOp (.elemAt 0)) [.var .none 0]]] vars state := by
  dsimp only
  let vars := [ClosSem.makeConst (.constCons 4 [child]), ClosSem.Value.block 0 [], ClosSem.listToValue env]
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
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 0 3)) [.var .none 0]) _ _ vars state false (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 3 1)) [.var .none 0]) _ _ vars state false (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 4 1)) [.var .none 0]) _ _ vars state true (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.trueTag])]
  simp only [↓reduceIte]
  rfl


/-- With enough clock, the tick branch interprets its encoded child after
three units spent entering the interpreter. -/
theorem interpreter_tick_reduce {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel source target) (child : ClosLang.Const) (env : List ClosSem.Value)
    (clock : 3 ≤ target.clock) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons 4 [child]), .block 0 [], ClosSem.listToValue env] target =
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst child, .block 0 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) := by
  rw [interpreter_tick_entry child env target]
  have childRun := evaluate_interpreter_field_call source target related 4 0 [child] child (by simp)
    (.block 0 []) env false clock
  simpa using childRun


/-- With an initial source clock of zero, the tick branch times out after one
interpreter call and leaves the related target at clock zero. -/
theorem interpreter_tick_timeout {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel source target) (child : ClosLang.Const) (env : List ClosSem.Value)
    (zero : source.clock = 0) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons 4 [child]), .block 0 [], ClosSem.listToValue env]
      { target with clock := 1 } = (.err (.abort .timeoutError), target) := by
  have targetZero : target.clock = 0 := by
    rcases related.1 with ⟨_, _, _, _, _, clocks, _⟩
    omega
  have targetReset : { target with clock := 0 } = target := by
    cases target
    simp_all
  have positive : 1 ≤ target.maxApp := by
    rcases related.1 with ⟨_, _, _, maxEq, maxPositive, _⟩
    omega
  let current := { target with clock := 1 }
  let vars := [ClosSem.makeConst (.constCons 4 [child]), ClosSem.Value.block 0 [], ClosSem.listToValue env]
  let global := ClosLang.Exp.op .none (.globOp (.global 0)) []
  let first := ClosLang.Exp.app .none none global [.var .none 2]
  let second := ClosLang.Exp.app .none none first [.op .none (.blockOp (.cons 0)) []]
  let encoded := ClosLang.Exp.op .none (.blockOp (.elemAt 0)) [.var .none 0]
  let original := ClosSem.Value.closure none [] [] 1 closInterpreter
  let firstValue := ClosSem.Value.closure none [] [ClosSem.listToValue env] 1
    (.fn (Flapjack.Basis.Pure.MlString.ofString "exp") none none 1 closInterpreterBody)
  have enlargedRel : StateRel { source with clock := 1 } current := by
    exact stateRel_withClock related 1
  have envRun : ClosSem.evaluate [.var .none 2] vars current = (.val [ClosSem.listToValue env], current) := by
    simp [vars, ClosSem.evaluate]
  have flagRun : ClosSem.evaluate [.op .none (.blockOp (.cons 0)) []] vars current = (.val [.block 0 []], current) :=
    evaluate_cons_nil .none 0 vars current
  have codeRun : ClosSem.evaluate [encoded] vars current = (.val [ClosSem.makeConst child], current) := by
    simp [encoded, vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock]
  have globalRun : ClosSem.evaluate [global] vars current = (.val [original], current) := by
    simpa [current, global, original] using evaluate_global_zero { source with clock := 1 } current enlargedRel .none vars 1
  have firstCall : ClosSem.destClosure current.maxApp none original [ClosSem.listToValue env] =
      some (.fullApp closInterpreter [ClosSem.listToValue env] []) := by
    simp [current, original, ClosSem.destClosure, ClosSem.checkLoc, positive]
  have firstRun : ClosSem.evaluate [first] vars current = (.val [firstValue], target) := by
    rw [show ClosSem.evaluate [first] vars current = ClosSem.evaluateApp none original [ClosSem.listToValue env] current from
      evaluate_unary_app _ _ _ _ _ _ _ _ envRun globalRun]
    rw [FlatToClos.evaluateApp_unary _ _ _ _ _ firstCall]
    simpa [current, closInterpreter, ClosSem.evaluate, ClosSem.decClock, positive, firstValue] using targetReset
  have secondCall : ClosSem.destClosure target.maxApp none firstValue [.block 0 []] =
      some (.fullApp (.fn (Flapjack.Basis.Pure.MlString.ofString "exp") none none 1 closInterpreterBody)
        [.block 0 [], ClosSem.listToValue env] []) := by
    simp [firstValue, ClosSem.destClosure, ClosSem.checkLoc, positive]
  have secondRun : ClosSem.evaluate [second] vars current = (.err (.abort .timeoutError), target) := by
    rw [show ClosSem.evaluate [second] vars current = ClosSem.evaluateApp none firstValue [.block 0 []] target from
      evaluate_unary_app _ _ _ _ _ _ _ _ flagRun firstRun]
    rw [FlatToClos.evaluateApp_unary _ _ _ _ _ secondCall]
    simp [targetZero]
  rw [interpreter_tick_entry child env current]
  change ClosSem.evaluate [.app .none none second [encoded]] vars current = _
  rw [ClosSem.evaluate]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
  rw [ClosSem.fixClock_evaluate, codeRun]
  rw [ClosSem.fixClock_evaluate, secondRun]


/-- Tick case of the interpreter simulation, including the zero-clock
 timeout and the induction hypothesis for its child. -/
theorem interpreter_correct_tick {C F : Type} (trace : BackendCommon.Tra) (child : ClosLang.Exp)
    (ih : ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [child] env source = (result, sourceFinal) → canInterpret child = true →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant child), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.tick trace child] env source = (result, sourceFinal))
    (valid : canInterpret (.tick trace child) = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant (.tick trace child)), .block 0 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  have clockEq : target.clock = source.clock := related.1.2.2.2.2.2.1
  by_cases zero : source.clock = 0
  · have sourceRun : ClosSem.evaluate [.tick trace child] env source =
        (.err (.abort .timeoutError), source) := by simp [ClosSem.evaluate, zero]
    rw [sourceRun] at run
    cases run
    refine ⟨1, target, ?_, related⟩
    have targetZero : target.clock = 0 := clockEq.trans zero
    simpa [toConstant, targetZero] using interpreter_tick_timeout source target related (toConstant child) env zero
  · have childRun : ClosSem.evaluate [child] env (ClosSem.decClock 1 source) = (result, sourceFinal) := by
      simpa [ClosSem.evaluate, zero] using run
    have childValid : canInterpret child = true := by simpa [canInterpret] using valid
    have childAssumption : InterpAssum C F (ClosSem.decClock 1 source).clock :=
      interpAssum_le assumption (by simp [ClosSem.decClock])
    have childRel : StateRel (ClosSem.decClock 1 source) (ClosSem.decClock 1 target) := by
      simpa only [ClosSem.decClock, clockEq] using stateRel_withClock related (source.clock - 1)
    obtain ⟨extra, targetFinal, targetRun, finalRel⟩ :=
      ih env (ClosSem.decClock 1 source) (ClosSem.decClock 1 target) sourceFinal result
        childRun childValid childAssumption childRel notTypeError
    let enlarged := { target with clock := 3 + (extra + (target.clock - 1)) }
    have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged := by
      exact stateRel_withClock related enlarged.clock
    have enough : 3 ≤ enlarged.clock := by simp [enlarged]
    have reduce := interpreter_tick_reduce { source with clock := enlarged.clock } enlarged enlargedRel
      (toConstant child) env enough
    have clocks : ClosSem.decClock 3 enlarged =
        { ClosSem.decClock 1 target with clock := extra + (ClosSem.decClock 1 target).clock } := by
      simp [ClosSem.decClock, enlarged]
    rw [clocks, targetRun] at reduce
    have originalClock : 3 + (extra + (target.clock - 1)) = (extra + 2) + target.clock := by omega
    refine ⟨extra + 2, targetFinal, ?_, finalRel⟩
    simpa [toConstant, enlarged, originalClock] using reduce

end Flapjack.Compiler.Backend.ClosInterp
