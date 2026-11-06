import Flapjack.Compiler.Backend.ClosInterp.Proofs.EvaluateBasic
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Call

/-! Correctness of the interpreter's environment lookup helper. Its evaluator
and value carriers remain proof-side and await cross-language review. -/
namespace Flapjack.Compiler.Backend.ClosInterp

/-- Looking up index zero returns the first encoded environment element. -/
theorem evaluate_closInterpEl_zero {C F : Type} (first : ClosSem.Value) (tail : List ClosSem.Value)
    (recursive : ClosSem.Value) (rest : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluate [closInterpEl]
      (ClosSem.listToValue (first :: tail) :: .number 0 :: recursive :: rest) state =
        (.val [first], state) := by
  change ClosSem.evaluate [
      .ifThenElse .none (.op .none (.blockOp (.equalConst (.int 0))) [.var .none 1])
        (.op .none (.blockOp (.elemAt 0)) [.var .none 0])
        (.app .none none (.app .none none (.var .none 2)
          [.op .none (.intOp .sub) [.op .none (.intOp (.const 1)) [], .var .none 1]])
          [.op .none (.blockOp (.elemAt 1)) [.var .none 0]])]
      (ClosSem.listToValue (first :: tail) :: .number 0 :: recursive :: rest) state = _
  simp [ClosSem.listToValue, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp,
    ClosSem.applyBlock, ClosSem.asBool, ClosSem.boolValue, BackendCommon.trueTag]


/-- A unary application evaluates its argument and function before applying
 the resulting value. -/
theorem evaluate_unary_app {C F : Type} (function argument : ClosLang.Exp)
    (env : List ClosSem.Value) (state afterArg afterFunction : ClosSem.State C F)
    (argValue fnValue : ClosSem.Value)
    (argRun : ClosSem.evaluate [argument] env state = (.val [argValue], afterArg))
    (fnRun : ClosSem.evaluate [function] env afterArg = (.val [fnValue], afterFunction)) :
    ClosSem.evaluate [.app .none none function [argument]] env state =
      ClosSem.evaluateApp none fnValue [argValue] afterFunction := by
  rw [ClosSem.evaluate]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
  rw [ClosSem.fixClock_evaluate, argRun]
  rw [ClosSem.fixClock_evaluate, fnRun]
  rfl


/-- A recursive interpreter call moves to the encoded tail, subtracts one
from the index, and spends two units of clock. -/
theorem evaluate_closInterpEl_step {C F : Type} (first : ClosSem.Value)
    (tail captured rest : List ClosSem.Value) (index : Nat) (state : ClosSem.State C F)
    (positive : 1 ≤ state.maxApp) (clock : 2 ≤ state.clock) :
    let recFun := ClosSem.Value.recclosure none [] captured
      [(1, .fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpEl)] 0
    ClosSem.evaluate [closInterpEl]
      (ClosSem.listToValue (first :: tail) :: .number (Int.ofNat (index + 1)) :: recFun :: rest) state =
    ClosSem.evaluate [closInterpEl]
      (ClosSem.listToValue tail :: .number (Int.ofNat index) :: recFun :: captured)
      (ClosSem.decClock 2 state) := by
  dsimp only
  let recFun := ClosSem.Value.recclosure none [] captured
      [(1, .fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpEl)] 0
  let env := ClosSem.listToValue (first :: tail) :: .number (Int.ofNat (index + 1)) :: recFun :: rest
  let tailExp := ClosLang.Exp.op .none (.blockOp (.elemAt 1)) [.var .none 0]
  let indexExp := ClosLang.Exp.op .none (.intOp .sub) [.op .none (.intOp (.const 1)) [], .var .none 1]
  let inner := ClosLang.Exp.app .none none (.var .none 2) [indexExp]
  let value := ClosSem.Value.closure none [] (.number (Int.ofNat index) :: recFun :: captured) 1 closInterpEl
  have tailRun : ClosSem.evaluate [tailExp] env state = (.val [ClosSem.listToValue tail], state) := by
    simp [tailExp, env, ClosSem.listToValue, ClosSem.evaluate, ClosSem.fixClock,
      ClosSem.doApp, ClosSem.applyBlock]
  have indexRun : ClosSem.evaluate [indexExp] env state = (.val [.number (Int.ofNat index)], state) := by
    simp [indexExp, env, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
      ClosSem.doIntApp]
  have varRun : ClosSem.evaluate [.var .none 2] env state = (.val [recFun], state) := by
    simp [env, ClosSem.evaluate]
  have recCall : ClosSem.destClosure state.maxApp none recFun [.number (Int.ofNat index)] =
      some (.fullApp (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpEl)
        (.number (Int.ofNat index) :: recFun :: captured) []) := by
    simp [recFun, ClosSem.destClosure, ClosSem.checkLoc, positive]
  have innerRun : ClosSem.evaluate [inner] env state = (.val [value], ClosSem.decClock 1 state) := by
    rw [show ClosSem.evaluate [inner] env state = ClosSem.evaluateApp none recFun [.number (Int.ofNat index)] state from
      evaluate_unary_app _ _ _ _ _ _ _ _ indexRun varRun]
    rw [FlatToClos.evaluateApp_unary _ _ _ _ _ recCall]
    have nonzero : state.clock ≠ 0 := by omega
    simp [ClosSem.evaluate, ClosSem.decClock, positive, value, nonzero]
  have call : ClosSem.destClosure (ClosSem.decClock 1 state).maxApp none value [ClosSem.listToValue tail] =
      some (.fullApp closInterpEl (ClosSem.listToValue tail :: .number (Int.ofNat index) :: recFun :: captured) []) := by
    simp [value, ClosSem.destClosure, ClosSem.checkLoc, ClosSem.decClock, positive]
  have nonzero : (0 : Int) ≠ (index : Int) + 1 := by
    have nonnegative : 0 ≤ (index : Int) := Int.natCast_nonneg _
    omega
  have condRun : ClosSem.evaluate [.op .none (.blockOp (.equalConst (.int 0))) [.var .none 1]] env state =
      (.val [.block 0 []], state) := by
    simp [env, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
      ClosSem.boolValue, BackendCommon.falseTag, nonzero]
  change ClosSem.evaluate [
      .ifThenElse .none (.op .none (.blockOp (.equalConst (.int 0))) [.var .none 1])
        (.op .none (.blockOp (.elemAt 0)) [.var .none 0]) (.app .none none inner [tailExp])] env state = _
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, condRun]
  change ClosSem.evaluate [.app .none none inner [tailExp]] env state = _
  rw [evaluate_unary_app inner tailExp env state state (ClosSem.decClock 1 state)
    (ClosSem.listToValue tail) value tailRun innerRun]
  rw [FlatToClos.evaluateApp_unary _ _ _ _ _ call]
  have remaining : state.clock - 1 ≠ 0 := by omega
  simp [ClosSem.decClock, Nat.sub_sub, remaining, recFun]


/-- The interpreter retrieves any in-range element of an encoded environment.
The extra clock is exactly two units per recursive step. -/
theorem evaluate_closInterpEl {C F : Type} (index : Nat) (values captured rest : List ClosSem.Value)
    (value : ClosSem.Value) (state : ClosSem.State C F)
    (positive : 1 ≤ state.maxApp) (found : values[index]? = some value) :
    ClosSem.evaluate [closInterpEl]
      (ClosSem.listToValue values :: .number (Int.ofNat index) ::
        .recclosure none [] captured [(1, .fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpEl)] 0 :: rest)
      { state with clock := state.clock + 2 * index } = (.val [value], state) := by
  induction index generalizing values rest with
  | zero =>
    cases values with
    | nil => simp at found
    | cons first tail =>
      simp at found
      subst value
      simpa using evaluate_closInterpEl_zero first tail
        (.recclosure none [] captured [(1, .fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpEl)] 0)
        rest state
  | succ index ih =>
    cases values with
    | nil => simp at found
    | cons first tail =>
      simp only [List.getElem?_cons_succ] at found
      have step := evaluate_closInterpEl_step first tail captured rest index
        { state with clock := state.clock + 2 * (index + 1) } (by simpa using positive) (by simp; omega)
      have clocks : ClosSem.decClock 2 { state with clock := state.clock + 2 * (index + 1) } =
          { state with clock := state.clock + 2 * index } := by
        simp only [ClosSem.decClock]
        congr 1
      rw [step, clocks]
      exact ih tail captured found


/-- An in-range environment lookup terminates with the original state after
some extra target clock. The proof-side evaluator and carriers still need HOL
correspondence review before this is classified as a theorem port. -/
theorem closInterpEl_correct {C F : Type} (index : Nat) (values captured rest : List ClosSem.Value)
    (state : ClosSem.State C F) (bound : index < values.length) (positive : 1 ≤ state.maxApp) :
    ∃ extra, ClosSem.evaluate [closInterpEl]
      (ClosSem.listToValue values :: .number (Int.ofNat index) ::
        .recclosure none [] captured [(1, .fn (Flapjack.Basis.Pure.MlString.ofString "") none none 1 closInterpEl)] 0 :: rest)
      { state with clock := extra + state.clock } = (.val [values[index]], state) := by
  refine ⟨2 * index, ?_⟩
  simpa [Nat.add_comm] using
    evaluate_closInterpEl index values captured rest values[index] state positive (by simp [bound])

end Flapjack.Compiler.Backend.ClosInterp
