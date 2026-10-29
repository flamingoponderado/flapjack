import Flapjack.Compiler.Backend.ClosInterp.Proofs.EvaluateEl

/-! Correctness of the interpreter's list reversal helper. The evaluator and
value carriers remain proof-side and await full HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp

/-- Reversal returns its accumulator unchanged on an empty input. -/
theorem evaluate_closInterpRev_nil {C F : Type} (acc : List ClosSem.Value)
    (recursive : ClosSem.Value) (rest : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluate [closInterpRev]
      (ClosSem.listToValue acc :: ClosSem.listToValue [] :: recursive :: rest) state =
        (.val [ClosSem.listToValue acc], state) := by
  change ClosSem.evaluate [
      .ifThenElse .none (.op .none (.blockOp (.lenEq 0)) [.var .none 1]) (.var .none 0)
        (.app .none none (.app .none none (.var .none 2)
          [.op .none (.blockOp (.elemAt 1)) [.var .none 1]])
          [.op .none (.blockOp (.cons 0)) [.var .none 0, .op .none (.blockOp (.elemAt 0)) [.var .none 1]]])]
      (ClosSem.listToValue acc :: ClosSem.listToValue [] :: recursive :: rest) state = _
  simp [ClosSem.listToValue, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp,
    ClosSem.applyBlock, ClosSem.asBool, ClosSem.boolValue, BackendCommon.trueTag]

/-- One recursive reversal step transfers the input head to the accumulator. -/
theorem evaluate_closInterpRev_step {C F : Type} (first : ClosSem.Value)
    (tail acc captured rest : List ClosSem.Value) (state : ClosSem.State C F)
    (positive : 1 ≤ state.maxApp) (clock : 2 ≤ state.clock) :
    let recFun := ClosSem.Value.recclosure none [] captured
      [(1, .fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpRev)] 0
    ClosSem.evaluate [closInterpRev]
      (ClosSem.listToValue acc :: ClosSem.listToValue (first :: tail) :: recFun :: rest) state =
    ClosSem.evaluate [closInterpRev]
      (ClosSem.listToValue (first :: acc) :: ClosSem.listToValue tail :: recFun :: captured)
      (ClosSem.decClock 2 state) := by
  dsimp only
  let recFun := ClosSem.Value.recclosure none [] captured
      [(1, .fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpRev)] 0
  let env := ClosSem.listToValue acc :: ClosSem.listToValue (first :: tail) :: recFun :: rest
  let accExp := ClosLang.Exp.op .none (.blockOp (.cons 0))
    [.var .none 0, .op .none (.blockOp (.elemAt 0)) [.var .none 1]]
  let tailExp := ClosLang.Exp.op .none (.blockOp (.elemAt 1)) [.var .none 1]
  let inner := ClosLang.Exp.app .none none (.var .none 2) [tailExp]
  let value := ClosSem.Value.closure none [] (ClosSem.listToValue tail :: recFun :: captured) 1 closInterpRev
  have accRun : ClosSem.evaluate [accExp] env state = (.val [ClosSem.listToValue (first :: acc)], state) := by
    simp [accExp, env, ClosSem.listToValue, ClosSem.evaluate, ClosSem.fixClock,
      ClosSem.doApp, ClosSem.applyBlock, BackendCommon.consTag]
  have tailRun : ClosSem.evaluate [tailExp] env state = (.val [ClosSem.listToValue tail], state) := by
    simp [tailExp, env, ClosSem.listToValue, ClosSem.evaluate, ClosSem.fixClock,
      ClosSem.doApp, ClosSem.applyBlock]
  have varRun : ClosSem.evaluate [.var .none 2] env state = (.val [recFun], state) := by
    simp [env, ClosSem.evaluate]
  have recCall : ClosSem.destClosure state.maxApp none recFun [ClosSem.listToValue tail] =
      some (.fullApp (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpRev)
        (ClosSem.listToValue tail :: recFun :: captured) []) := by
    simp [recFun, ClosSem.destClosure, ClosSem.checkLoc, positive]
  have innerRun : ClosSem.evaluate [inner] env state = (.val [value], ClosSem.decClock 1 state) := by
    rw [show ClosSem.evaluate [inner] env state = ClosSem.evaluateApp none recFun [ClosSem.listToValue tail] state from
      evaluate_unary_app _ _ _ _ _ _ _ _ tailRun varRun]
    rw [FlatToClos.evaluateApp_unary _ _ _ _ _ recCall]
    have nonzero : state.clock ≠ 0 := by omega
    simp [ClosSem.evaluate, ClosSem.decClock, positive, value, nonzero]
  have call : ClosSem.destClosure (ClosSem.decClock 1 state).maxApp none value [ClosSem.listToValue (first :: acc)] =
      some (.fullApp closInterpRev (ClosSem.listToValue (first :: acc) :: ClosSem.listToValue tail :: recFun :: captured) []) := by
    simp [value, ClosSem.destClosure, ClosSem.checkLoc, ClosSem.decClock, positive]
  have condRun : ClosSem.evaluate [.op .none (.blockOp (.lenEq 0)) [.var .none 1]] env state =
      (.val [.block 0 []], state) := by
    simp [env, ClosSem.listToValue, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp,
      ClosSem.applyBlock, ClosSem.boolValue, BackendCommon.falseTag]
  change ClosSem.evaluate [
      .ifThenElse .none (.op .none (.blockOp (.lenEq 0)) [.var .none 1]) (.var .none 0)
        (.app .none none inner [accExp])] env state = _
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, condRun]
  change ClosSem.evaluate [.app .none none inner [accExp]] env state = _
  rw [evaluate_unary_app inner accExp env state state (ClosSem.decClock 1 state)
    (ClosSem.listToValue (first :: acc)) value accRun innerRun]
  rw [FlatToClos.evaluateApp_unary _ _ _ _ _ call]
  have remaining : state.clock - 1 ≠ 0 := by omega
  simp [ClosSem.decClock, Nat.sub_sub, remaining, recFun]


/-- The interpreter reverses an encoded list onto its accumulator, spending
exactly two clock units for each element. -/
theorem evaluate_closInterpRev {C F : Type} (items acc captured rest : List ClosSem.Value)
    (state : ClosSem.State C F) (positive : 1 ≤ state.maxApp) :
    ClosSem.evaluate [closInterpRev]
      (ClosSem.listToValue acc :: ClosSem.listToValue items ::
        .recclosure none [] captured [(1, .fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpRev)] 0 :: rest)
      { state with clock := 2 * items.length + state.clock } =
        (.val [ClosSem.listToValue (items.reverse ++ acc)], state) := by
  induction items generalizing acc rest with
  | nil =>
    simpa using evaluate_closInterpRev_nil acc
      (.recclosure none [] captured [(1, .fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpRev)] 0)
      rest state
  | cons first tail ih =>
    have step := evaluate_closInterpRev_step first tail acc captured rest
      { state with clock := 2 * (tail.length + 1) + state.clock } (by simpa using positive) (by simp; omega)
    have clocks : ClosSem.decClock 2 { state with clock := 2 * (tail.length + 1) + state.clock } =
        { state with clock := 2 * tail.length + state.clock } := by
      simp only [ClosSem.decClock]
      congr 1
      omega
    simp only [List.length_cons]
    rw [step, clocks]
    simpa [List.reverse_cons, List.append_assoc] using ih (first :: acc) captured

end Flapjack.Compiler.Backend.ClosInterp
