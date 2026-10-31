import Flapjack.Compiler.Backend.Semantics.BviProps.AdjustOracle
import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateClockFull

/-! Evaluator cases for BVI compiler-oracle adjustment. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value unitValue asBool)

/-- Oracle-adjustment simulation at a bounded source clock. This Flapjack
induction invariant remains untagged pending BVI evaluator correspondence. -/
def oracleEvalThrough {C D F : Type} (compiler : Compiler D) (f : C → D)
    (limit : Nat) (expressions : List Bvi.Exp) : Prop :=
  ∀ (env : List Value) (state next : BviState C F) (result : BviResult),
    state.clock ≤ limit → evaluate expressions env state = (result, next) →
    result ≠ .err (.abort .typeError) → adjustOracleOk compiler f state →
    evaluate expressions env (adjustOracle compiler f state) =
      (result, adjustOracle compiler f next) ∧ adjustOracleOk compiler f next

/-- A bounded structural step and smaller-clock induction establish the
simulation at every bound. The step for calls and force remains open. -/
theorem oracleEvalThrough_of_step {C D F : Type} (compiler : Compiler D) (f : C → D)
    (step : ∀ limit xs,
      (∀ ys, sizeOf ys < sizeOf xs → oracleEvalThrough (F := F) compiler f limit ys) →
      (∀ smaller, smaller < limit → ∀ ys, oracleEvalThrough (F := F) compiler f smaller ys) →
      oracleEvalThrough (F := F) compiler f limit xs) :
    ∀ limit xs, oracleEvalThrough (F := F) compiler f limit xs := by
  intro limit
  induction limit using Nat.strong_induction_on with
  | h limit clockIH =>
    have bySize : ∀ n xs, sizeOf xs = n → oracleEvalThrough (F := F) compiler f limit xs := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n sizeIH =>
        intro xs sizeEq
        apply step limit xs
        · intro ys smaller
          exact sizeIH (sizeOf ys) (by omega) ys rfl
        · exact clockIH
    intro xs
    exact bySize (sizeOf xs) xs rfl

/-- The empty expression list preserves the oracle relation. -/
theorem oracleEval_nil {C D F : Type} (compiler : Compiler D) (f : C → D) (limit : Nat) :
    oracleEvalThrough (F := F) compiler f limit [] := by
  intro env state next result _ run _ ok
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨by simp [evaluate], ok⟩

/-- Variable lookup preserves the oracle relation. -/
theorem oracleEval_var {C D F : Type} (compiler : Compiler D) (f : C → D) (limit index : Nat) :
    oracleEvalThrough (F := F) compiler f limit [.var index] := by
  intro env state next result _ run _ ok
  cases found : env[index]? <;> simp [evaluate, found] at run ⊢ <;>
    obtain ⟨rfl, rfl⟩ := run <;> simp [ok]

/-- A raised expression uses the bounded simulation of its operand. -/
theorem oracleEval_raise {C D F : Type} (compiler : Compiler D) (f : C → D) (limit : Nat)
    (body : Bvi.Exp) (ih : oracleEvalThrough (F := F) compiler f limit [body]) :
    oracleEvalThrough (F := F) compiler f limit [.raise body] := by
  intro env state next result bound run notType ok
  cases childRun : evaluate [body] env state with
  | mk childResult childNext =>
    have childNotType : childResult ≠ .err (.abort .typeError) := by
      intro bad
      subst childResult
      simp [evaluate, childRun] at run
      exact notType run.1.symm
    obtain ⟨adjusted, childOk⟩ := ih env state childNext childResult bound childRun childNotType ok
    rw [evaluate, childRun] at run
    rw [evaluate, adjusted]
    cases childResult <;> simp_all

/-- Returning a list uses the bounded simulation of its operands. -/
theorem oracleEval_return {C D F : Type} (compiler : Compiler D) (f : C → D) (limit : Nat)
    (args : List Bvi.Exp) (ih : oracleEvalThrough (F := F) compiler f limit args) :
    oracleEvalThrough (F := F) compiler f limit [.return args] := by
  intro env state next result bound run notType ok
  cases childRun : evaluate args env state with
  | mk childResult childNext =>
    have childNotType : childResult ≠ .err (.abort .typeError) := by
      intro bad
      subst childResult
      simp [evaluate, childRun] at run
      exact notType run.1.symm
    obtain ⟨adjusted, childOk⟩ := ih env state childNext childResult bound childRun childNotType ok
    rw [evaluate, childRun] at run
    rw [evaluate, adjusted]
    cases childResult <;> simp_all

/-- A tick decrements both corresponding clocks before evaluating its body. -/
theorem oracleEval_tick {C D F : Type} (compiler : Compiler D) (f : C → D) (limit : Nat)
    (body : Bvi.Exp) (ih : oracleEvalThrough (F := F) compiler f limit [body]) :
    oracleEvalThrough (F := F) compiler f limit [.tick body] := by
  intro env state next result bound run notType ok
  by_cases zero : state.clock = 0
  · simp [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨by simp [evaluate, adjustOracle, zero], ok⟩
  · have bodyRun : evaluate [body] env (decClock 1 state) = (result, next) := by
      simpa [evaluate, zero] using run
    have bodyBound : (decClock 1 state).clock ≤ limit := by simp [decClock]; omega
    have bodyOk : adjustOracleOk compiler f (decClock 1 state) := by simpa [decClock, adjustOracleOk] using ok
    obtain ⟨adjusted, nextOk⟩ := ih env (decClock 1 state) next result bodyBound bodyRun notType bodyOk
    refine ⟨?_, nextOk⟩
    simpa [evaluate, adjustOracle, zero, decClock] using adjusted

/-- Operation evaluation uses the bounded operand simulation followed by
the primitive oracle-adjustment theorem. -/
theorem oracleEval_op {C D F : Type} (compiler : Compiler D) (f : C → D) (limit : Nat)
    (operation : ClosLang.Op) (args : List Bvi.Exp)
    (ih : oracleEvalThrough (F := F) compiler f limit args) :
    oracleEvalThrough (F := F) compiler f limit [.op operation args] := by
  intro env state next result bound run notType ok
  rw [evaluate, fixClock_evaluate] at run ⊢
  cases argsRun : evaluate args env state with
  | mk argsResult middle =>
    have argsNotType : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      simp [argsRun] at run
      exact notType run.1.symm
    obtain ⟨adjustedArgs, middleOk⟩ := ih env state middle argsResult bound argsRun argsNotType ok
    rw [adjustedArgs]
    cases argsResult with
    | err error =>
      simp only [argsRun] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨rfl, middleOk⟩
    | val values =>
      cases applied : doApp operation values.reverse middle with
      | err error =>
        have same : (.err error, middle) = (result, next) := by simpa [argsRun, applied] using run
        have errorOk : error ≠ .abort .typeError := by
          intro bad
          apply notType
          exact (congrArg Prod.fst same).symm.trans (by simp [bad])
        have adjustedApp := doApp_adjustOracle_error compiler f operation values.reverse middle error errorOk applied
        cases same
        exact ⟨by simp [adjustedApp], middleOk⟩
      | val pair =>
        obtain ⟨value, last⟩ := pair
        have same : (.val [value], last) = (result, next) := by simpa [argsRun, applied] using run
        obtain ⟨adjustedApp, lastOk⟩ :=
          doApp_adjustOracle_success compiler f operation values.reverse middle last value middleOk applied
        cases same
        exact ⟨by simp [adjustedApp], lastOk⟩

/-- Local bindings propagate the oracle relation to the body at the
remaining clock. -/
theorem oracleEval_let {C D F : Type} (compiler : Compiler D) (f : C → D) (limit : Nat)
    (bindings : List Bvi.Exp) (body : Bvi.Exp)
    (bindingsIH : oracleEvalThrough (F := F) compiler f limit bindings)
    (bodyIH : oracleEvalThrough (F := F) compiler f limit [body]) :
    oracleEvalThrough (F := F) compiler f limit [.let bindings body] := by
  intro env state next result bound run notType ok
  rw [evaluate, fixClock_evaluate] at run ⊢
  cases bindingsRun : evaluate bindings env state with
  | mk bindingsResult middle =>
    have bindingsNotType : bindingsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bindingsResult
      simp [bindingsRun] at run
      exact notType run.1.symm
    obtain ⟨adjustedBindings, middleOk⟩ :=
      bindingsIH env state middle bindingsResult bound bindingsRun bindingsNotType ok
    rw [adjustedBindings]
    cases bindingsResult with
    | err error =>
      simp only [bindingsRun] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨rfl, middleOk⟩
    | val values =>
      have middleClock := evaluate_clock_le bindings env state
      rw [bindingsRun] at middleClock
      have middleBound : middle.clock ≤ limit := Nat.le_trans middleClock bound
      have bodyRun : evaluate [body] (values ++ env) middle = (result, next) := by
        simpa [bindingsRun] using run
      exact bodyIH (values ++ env) middle next result middleBound bodyRun notType middleOk

/-- Sequential expression lists preserve the relation through both runs. -/
theorem oracleEval_cons {C D F : Type} (compiler : Compiler D) (f : C → D) (limit : Nat)
    (first second : Bvi.Exp) (rest : List Bvi.Exp)
    (headIH : oracleEvalThrough (F := F) compiler f limit [first])
    (tailIH : oracleEvalThrough (F := F) compiler f limit (second :: rest)) :
    oracleEvalThrough (F := F) compiler f limit (first :: second :: rest) := by
  intro env state next result bound run notType ok
  rw [evaluate, fixClock_evaluate] at run ⊢
  cases headRun : evaluate [first] env state with
  | mk headResult middle =>
    have headNotType : headResult ≠ .err (.abort .typeError) := by
      intro bad
      subst headResult
      simp [headRun] at run
      exact notType run.1.symm
    obtain ⟨adjustedHead, middleOk⟩ := headIH env state middle headResult bound headRun headNotType ok
    rw [adjustedHead]
    cases headResult with
    | err error =>
      simp only [headRun] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨rfl, middleOk⟩
    | val values =>
      have middleClock := evaluate_clock_le [first] env state
      rw [headRun] at middleClock
      have middleBound : middle.clock ≤ limit := Nat.le_trans middleClock bound
      cases tailRun : evaluate (second :: rest) env middle with
      | mk tailResult last =>
        have tailNotType : tailResult ≠ .err (.abort .typeError) := by
          intro bad
          subst tailResult
          simp [headRun, tailRun] at run
          exact notType run.1.symm
        obtain ⟨adjustedTail, lastOk⟩ := tailIH env middle last tailResult middleBound tailRun tailNotType middleOk
        rw [adjustedTail]
        cases tailResult <;> simp_all

/-- Conditional evaluation preserves the relation through the guard and the
selected branch. -/
theorem oracleEval_if {C D F : Type} (compiler : Compiler D) (f : C → D) (limit : Nat)
    (condition yes no : Bvi.Exp)
    (guardIH : oracleEvalThrough (F := F) compiler f limit [condition])
    (yesIH : oracleEvalThrough (F := F) compiler f limit [yes])
    (noIH : oracleEvalThrough (F := F) compiler f limit [no]) :
    oracleEvalThrough (F := F) compiler f limit [.ifThenElse condition yes no] := by
  intro env state next result bound run notType ok
  rw [evaluate, fixClock_evaluate] at run ⊢
  cases guardRun : evaluate [condition] env state with
  | mk guardResult middle =>
    have guardNotType : guardResult ≠ .err (.abort .typeError) := by
      intro bad
      subst guardResult
      simp [guardRun] at run
      exact notType run.1.symm
    obtain ⟨adjustedGuard, middleOk⟩ := guardIH env state middle guardResult bound guardRun guardNotType ok
    rw [adjustedGuard]
    rw [guardRun] at run
    cases guardResult with
    | err error =>
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨rfl, middleOk⟩
    | val values =>
      have middleClock := evaluate_clock_le [condition] env state
      rw [guardRun] at middleClock
      have middleBound : middle.clock ≤ limit := Nat.le_trans middleClock bound
      change (match asBool (@Flapjack.holHd Value ⟨unitValue⟩ values) with
        | none => (.err (.abort .typeError), middle)
        | some true => evaluate [yes] env middle
        | some false => evaluate [no] env middle) = (result, next) at run
      change (match asBool (@Flapjack.holHd Value ⟨unitValue⟩ values) with
        | none => ((.err (.abort .typeError) : BviResult), adjustOracle compiler f middle)
        | some true => evaluate [yes] env (adjustOracle compiler f middle)
        | some false => evaluate [no] env (adjustOracle compiler f middle)) = _ ∧ _
      cases truth : asBool (@Flapjack.holHd Value ⟨unitValue⟩ values) with
      | none =>
        simp [truth] at run
        exact (notType run.1.symm).elim
      | some choice =>
        cases choice with
        | false =>
          simp only [truth] at run ⊢
          exact noIH env middle next result middleBound run notType middleOk
        | true =>
          simp only [truth] at run ⊢
          exact yesIH env middle next result middleBound run notType middleOk

end Flapjack.Compiler.Backend.BviProps
