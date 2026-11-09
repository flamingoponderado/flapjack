import Flapjack.Compiler.Backend.ClosInterp.Proofs.InterpreterCall

/-! The interpreter's raise-expression dispatch. Its evaluator and state
carriers remain proof-side and await HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- A raise encoding selects the branch that recursively interprets its
single encoded child. -/
theorem interpreter_raise_entry {C F : Type} (child : ClosLang.Const) (env : List ClosSem.Value)
    (state : ClosSem.State C F) :
    let vars := [ClosSem.makeConst (.constCons 3 [child]), .block 0 [], ClosSem.listToValue env]
    let global := ClosLang.Exp.op .none (.globOp (.global 0)) []
    let first := ClosLang.Exp.app .none none global [.var .none 2]
    let second := ClosLang.Exp.app .none none first [.op .none (.blockOp (.cons 0)) []]
    ClosSem.evaluate [closInterpreterBody] vars state =
      ClosSem.evaluate [.raise .none (.app .none none second [.op .none (.blockOp (.elemAt 0)) [.var .none 0]])] vars state := by
  dsimp only
  let vars := [ClosSem.makeConst (.constCons 3 [child]), ClosSem.Value.block 0 [], ClosSem.listToValue env]
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
  rw [evaluate_if_condition (.op .none (.blockOp (.tagLenEq 3 1)) [.var .none 0]) _ _ vars state true (by
    simp [vars, ClosSem.makeConst, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.trueTag])]
  simp only [↓reduceIte]
  rfl


/-- The raise branch interprets its child with three fewer clock units, then
propagates an error or raises the child's value. -/
theorem interpreter_raise_reduce {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel source target) (child : ClosLang.Const) (env : List ClosSem.Value)
    (clock : 3 ≤ target.clock) :
    ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (.constCons 3 [child]), .block 0 [], ClosSem.listToValue env] target =
      match ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst child, .block 0 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) with
      | (.err error, last) => (.err error, last)
      | (.val values, last) => (.err (.raise (@Flapjack.holHd ClosSem.Value ⟨ClosSem.unitValue⟩ values)), last) := by
  rw [interpreter_raise_entry child env target]
  rw [ClosSem.evaluate]
  have childRun := evaluate_interpreter_field_call source target related 3 0 [child] child (by simp)
    (.block 0 []) env false clock
  simp only [Bool.false_eq_true, ↓reduceIte] at childRun
  rw [childRun]
  cases run : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst child, .block 0 [], ClosSem.listToValue env] (ClosSem.decClock 3 target) with
  | mk result last => cases result <;> rfl


/-- Raise case of the interpreter simulation, using the induction hypothesis
for its child expression. -/
theorem interpreter_correct_raise {C F : Type} (trace : BackendCommon.Tra) (child : ClosLang.Exp)
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
    (run : ClosSem.evaluate [.raise trace child] env source = (result, sourceFinal))
    (valid : canInterpret (.raise trace child) = true)
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant (.raise trace child)), .block 0 [], ClosSem.listToValue env]
        { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  cases childRun : ClosSem.evaluate [child] env source with
  | mk childResult childFinal =>
    have childNotTypeError : childResult ≠ .err (.abort .typeError) := by
      intro bad
      subst childResult
      simp [ClosSem.evaluate, childRun] at run
      exact notTypeError run.1.symm
    have childValid : canInterpret child = true := by simpa [canInterpret] using valid
    obtain ⟨extra, targetFinal, targetRun, finalRel⟩ :=
      ih env source target childFinal childResult childRun childValid assumption related childNotTypeError
    let enlarged := { target with clock := 3 + (extra + target.clock) }
    have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged := by
      exact stateRel_withClock related enlarged.clock
    have enough : 3 ≤ enlarged.clock := by simp [enlarged]
    have reduce := interpreter_raise_reduce { source with clock := enlarged.clock } enlarged enlargedRel
      (toConstant child) env enough
    have clocks : ClosSem.decClock 3 enlarged = { target with clock := extra + target.clock } := by
      simp [ClosSem.decClock, enlarged]
    rw [clocks, targetRun] at reduce
    rw [ClosSem.evaluate, childRun] at run
    cases childResult with
    | err error =>
      simp only at run reduce
      cases run
      refine ⟨3 + extra, targetFinal, ?_, finalRel⟩
      simpa [toConstant, enlarged, Nat.add_assoc] using reduce
    | val values =>
      simp only at run reduce
      cases run
      refine ⟨3 + extra, targetFinal, ?_, finalRel⟩
      cases values with
      | nil =>
        change ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant (.raise trace child)), .block 0 [], ClosSem.listToValue env]
          { target with clock := (3 + extra) + target.clock } =
            (.err (.raise (@Flapjack.holHd ClosSem.Value ⟨ClosSem.unitValue⟩ [])), targetFinal)
        simpa [toConstant, enlarged, Nat.add_assoc] using reduce
      | cons value rest => simpa [toConstant, enlarged, Nat.add_assoc, Flapjack.holHd] using reduce

end Flapjack.Compiler.Backend.ClosInterp
