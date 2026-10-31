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
simulation at every bound. -/
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

/-- Smaller-clock induction for a dynamically selected function body. -/
def oracleEvalBody {C D F : Type} (compiler : Compiler D) (f : C → D) (limit : Nat) : Prop :=
  ∀ (body : Bvi.Exp) (env : List Value) (state next : BviState C F) (result : BviResult),
    state.clock < limit → evaluate [body] env state = (result, next) →
    result ≠ .err (.abort .typeError) → adjustOracleOk compiler f state →
    evaluate [body] env (adjustOracle compiler f state) =
      (result, adjustOracle compiler f next) ∧ adjustOracleOk compiler f next

/-- Forcing a thunk invokes its body under the smaller-clock hypothesis. -/
theorem oracleEval_force {C D F : Type} (compiler : Compiler D) (f : C → D)
    (location index : Nat) (env : List Value) (state next : BviState C F) (result : BviResult)
    (bodyIH : oracleEvalBody (F := F) compiler f state.clock)
    (run : evaluate [.force location index] env state = (result, next))
    (notType : result ≠ .err (.abort .typeError)) (ok : adjustOracleOk compiler f state) :
    evaluate [.force location index] env (adjustOracle compiler f state) =
      (result, adjustOracle compiler f next) ∧ adjustOracleOk compiler f next := by
  cases lookup : env[index]? with
  | none =>
    simp [evaluate, lookup] at run
    exact (notType run.1.symm).elim
  | some thunk =>
    cases thunkRun : destThunk thunk state.refs with
    | badRef =>
      simp [evaluate, lookup, thunkRun] at run
      exact (notType run.1.symm).elim
    | notThunk =>
      simp [evaluate, lookup, thunkRun] at run
      exact (notType run.1.symm).elim
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        simp [evaluate, lookup, thunkRun] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨by simp [evaluate, lookup, thunkRun, adjustOracle], ok⟩
      | notEvaluated =>
        cases found : BvlSem.findCode (some location) [thunk, value] state.code with
        | none =>
          simp [evaluate, lookup, thunkRun, found] at run
          exact (notType run.1.symm).elim
        | some pair =>
          obtain ⟨args, body⟩ := pair
          by_cases zero : state.clock = 0
          · simp [evaluate, lookup, thunkRun, found, zero] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨by simp [evaluate, lookup, thunkRun, found, zero, adjustOracle],
              by simpa [adjustOracleOk] using ok⟩
          · have smaller : (decClock 1 state).clock < state.clock := by simp [decClock]; omega
            have bodyOk : adjustOracleOk compiler f (decClock 1 state) := by
              simpa [decClock, adjustOracleOk] using ok
            cases bodyRun : evaluate [body] args (decClock 1 state) with
            | mk bodyResult bodyNext =>
              have bodyNotType : bodyResult ≠ .err (.abort .typeError) := by
                intro bad
                subst bodyResult
                simp [evaluate, lookup, thunkRun, found, zero, bodyRun] at run
                exact notType run.1.symm
              obtain ⟨adjusted, finalOk⟩ := bodyIH body args (decClock 1 state) bodyNext bodyResult
                smaller bodyRun bodyNotType bodyOk
              simp only [evaluate, lookup, thunkRun, found, zero, bodyRun] at run
              have same : (bodyResult, bodyNext) = (result, next) := by
                cases bodyResult with
                | val values => exact run
                | err error =>
                  cases error with
                  | abort reason => exact run
                  | raise payload =>
                    cases payload with
                    | exn exception => exact run
                    | ret values =>
                      simp at run
                      exact (notType run.1.symm).elim
              have notReturn : ∀ values, bodyResult ≠ .err (.raise (.ret values)) := by
                intro values eq
                rw [eq] at run
                simp at run
                exact notType run.1.symm
              cases same
              refine ⟨?_, finalOk⟩
              simp only [evaluate, lookup, adjustOracle, thunkRun, found, zero, ↓reduceIte]
              simp only [adjustOracle, decClock] at adjusted
              dsimp only [decClock]
              rw [adjusted]
              cases result with
              | val values => rfl
              | err error =>
                cases error with
                | abort reason => rfl
                | raise payload =>
                  cases payload with
                  | exn exception => rfl
                  | ret values => exact (notReturn values rfl).elim

/-- A let-call uses the smaller-clock induction for its callee and its
continuation after successful return. -/
theorem oracleEval_letCall {C D F : Type} (compiler : Compiler D) (f : C → D) (limit : Nat)
    (rets ticks dest : Nat) (args : List Bvi.Exp) (body : Bvi.Exp) (env : List Value)
    (state next : BviState C F) (result : BviResult)
    (bound : state.clock ≤ limit) (argsIH : oracleEvalThrough (F := F) compiler f limit args)
    (bodyIH : oracleEvalBody (F := F) compiler f state.clock)
    (run : evaluate [.letCall rets ticks dest args body] env state = (result, next))
    (notType : result ≠ .err (.abort .typeError)) (ok : adjustOracleOk compiler f state) :
    evaluate [.letCall rets ticks dest args body] env (adjustOracle compiler f state) =
      (result, adjustOracle compiler f next) ∧ adjustOracleOk compiler f next := by
  cases argsRun : evaluate args env state with
  | mk argResult argNext =>
    have argBound : argNext.clock ≤ state.clock := by
      have clock := evaluate_clock_le args env state
      simpa [argsRun] using clock
    rw [evaluate, fixClock_evaluate, argsRun] at run
    have argNotType : argResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argResult
      simp at run
      exact notType run.1.symm
    obtain ⟨adjustedArgs, argOk⟩ := argsIH env state argNext argResult bound argsRun argNotType ok
    rw [evaluate, fixClock_evaluate, adjustedArgs]
    cases argResult with
    | err error => simp_all
    | val values =>
      cases found : BvlSem.findCode (some dest) values argNext.code with
      | none =>
        simp [found] at run
        exact (notType run.1.symm).elim
      | some selected =>
        obtain ⟨callValues, callee⟩ := selected
        by_cases timeout : argNext.clock < ticks + 1
        · simp [found, timeout] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨?_, by simpa [adjustOracleOk] using argOk⟩
          simp [adjustOracle, found, timeout]
        · have smaller : (decClock (ticks + 1) argNext).clock < state.clock := by
            simp only [decClock]
            omega
          have calleeOk : adjustOracleOk compiler f (decClock (ticks + 1) argNext) := by
            simpa [adjustOracleOk, decClock] using argOk
          simp only [found, timeout, ↓reduceIte, fixClock_evaluate] at run
          simp only [adjustOracle, found, timeout, ↓reduceIte, fixClock_evaluate]
          cases bodyRun : evaluate [callee] callValues (decClock (ticks + 1) argNext) with
          | mk bodyResult bodyNext =>
            rw [bodyRun] at run
            have bodyNotType : bodyResult ≠ .err (.abort .typeError) := by
              intro bad
              subst bodyResult
              simp at run
              exact notType run.1.symm
            obtain ⟨adjustedBody, bodyOk⟩ := bodyIH callee callValues (decClock (ticks + 1) argNext)
              bodyNext bodyResult smaller bodyRun bodyNotType calleeOk
            simp only [adjustOracle, decClock] at adjustedBody
            dsimp only [decClock]
            rw [adjustedBody]
            cases bodyResult with
            | val values =>
              simp at run
              exact (notType run.1.symm).elim
            | err error =>
              cases error with
              | abort reason => simp_all [adjustOracle]
              | raise payload =>
                cases payload with
                | exn value => simp_all [adjustOracle]
                | ret values =>
                  by_cases arity : values.length = rets
                  · have calledClock : bodyNext.clock < state.clock := by
                      have clock := evaluate_clock_le [callee] callValues (decClock (ticks + 1) argNext)
                      rw [bodyRun] at clock
                      simp only [decClock] at clock
                      omega
                    have continuationRun : evaluate [body] (values ++ env) bodyNext = (result, next) := by
                      simpa [arity] using run
                    have continuation := bodyIH body (values ++ env) bodyNext next result
                      calledClock continuationRun notType bodyOk
                    simpa [arity, adjustOracle] using continuation
                  · simp [arity] at run
                    exact (notType run.1.symm).elim

/-- A call uses the smaller-clock induction for its callee and, when an
exception is caught, for the handler. -/
theorem oracleEval_call {C D F : Type} (compiler : Compiler D) (f : C → D) (limit : Nat)
    (ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp) (handler : Option Bvi.Exp)
    (env : List Value) (state next : BviState C F) (result : BviResult)
    (bound : state.clock ≤ limit) (argsIH : oracleEvalThrough (F := F) compiler f limit args)
    (bodyIH : oracleEvalBody (F := F) compiler f state.clock)
    (run : evaluate [.call ticks dest args handler] env state = (result, next))
    (notType : result ≠ .err (.abort .typeError)) (ok : adjustOracleOk compiler f state) :
    evaluate [.call ticks dest args handler] env (adjustOracle compiler f state) =
      (result, adjustOracle compiler f next) ∧ adjustOracleOk compiler f next := by
  by_cases invalid : dest.isNone && handler.isSome
  · simp [evaluate, invalid] at run
    exact (notType run.1.symm).elim
  · cases argsRun : evaluate args env state with
    | mk argResult argNext =>
      have argBound : argNext.clock ≤ state.clock := by
        have clock := evaluate_clock_le args env state
        simpa [argsRun] using clock
      rw [evaluate] at run
      simp only [invalid, Bool.false_eq_true, ↓reduceIte] at run
      rw [fixClock_evaluate, argsRun] at run
      have argNotType : argResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argResult
        simp at run
        exact notType run.1.symm
      obtain ⟨adjustedArgs, argOk⟩ := argsIH env state argNext argResult bound argsRun argNotType ok
      rw [evaluate]
      simp only [invalid, Bool.false_eq_true, ↓reduceIte]
      rw [fixClock_evaluate, adjustedArgs]
      cases argResult with
      | err error => simp_all
      | val values =>
        cases found : BvlSem.findCode dest values argNext.code with
        | none =>
          simp [found] at run
          exact (notType run.1.symm).elim
        | some selected =>
          obtain ⟨callValues, body⟩ := selected
          by_cases timeout : argNext.clock < ticks + 1
          · simp [found, timeout] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨?_, by simpa [adjustOracleOk] using argOk⟩
            simp [adjustOracle, found, timeout]
          · have smaller : (decClock (ticks + 1) argNext).clock < state.clock := by
              simp only [decClock]
              omega
            have calleeOk : adjustOracleOk compiler f (decClock (ticks + 1) argNext) := by
              simpa [adjustOracleOk, decClock] using argOk
            simp only [found, timeout, ↓reduceIte, fixClock_evaluate] at run
            simp only [adjustOracle, found, timeout, ↓reduceIte, fixClock_evaluate]
            cases bodyRun : evaluate [body] callValues (decClock (ticks + 1) argNext) with
            | mk bodyResult bodyNext =>
              rw [bodyRun] at run
              have bodyNotType : bodyResult ≠ .err (.abort .typeError) := by
                intro bad
                subst bodyResult
                simp at run
                exact notType run.1.symm
              obtain ⟨adjustedBody, bodyOk⟩ := bodyIH body callValues (decClock (ticks + 1) argNext)
                bodyNext bodyResult smaller bodyRun bodyNotType calleeOk
              simp only [adjustOracle, decClock] at adjustedBody
              dsimp only [decClock]
              rw [adjustedBody]
              cases bodyResult with
              | val values => simp_all [adjustOracle]
              | err error =>
                cases error with
                | abort reason => simp_all [adjustOracle]
                | raise payload =>
                  cases payload with
                  | ret values =>
                    simp at run
                    exact (notType run.1.symm).elim
                  | exn value =>
                    cases handler with
                    | none => simp_all [adjustOracle]
                    | some handler =>
                      have calledClock : bodyNext.clock < state.clock := by
                        have clock := evaluate_clock_le [body] callValues (decClock (ticks + 1) argNext)
                        rw [bodyRun] at clock
                        simp only [decClock] at clock
                        omega
                      cases handlerRun : evaluate [handler] (value :: env) bodyNext with
                      | mk handlerResult handlerNext =>
                        have handlerNotType : handlerResult ≠ .err (.abort .typeError) := by
                          intro bad
                          subst handlerResult
                          simp [handlerRun] at run
                          exact notType run.1.symm
                        obtain ⟨adjustedHandler, handlerOk⟩ := bodyIH handler (value :: env) bodyNext
                          handlerNext handlerResult calledClock handlerRun handlerNotType bodyOk
                        simp only [handlerRun] at run
                        simp only [adjustOracle] at adjustedHandler
                        dsimp only
                        rw [adjustedHandler]
                        cases handlerResult with
                        | val values => simp_all [adjustOracle]
                        | err error =>
                          cases error with
                          | abort reason => simp_all [adjustOracle]
                          | raise payload => cases payload <;> simp_all [adjustOracle]

/-- All singleton cases follow from structural and smaller-clock induction. -/
theorem oracleEval_singleton {C D F : Type} (compiler : Compiler D) (f : C → D)
    (limit : Nat) (e : Bvi.Exp)
    (structuralIH : ∀ xs, sizeOf xs < sizeOf [e] → oracleEvalThrough (F := F) compiler f limit xs)
    (clockIH : ∀ smaller, smaller < limit → ∀ xs, oracleEvalThrough (F := F) compiler f smaller xs) :
    oracleEvalThrough (F := F) compiler f limit [e] := by
  intro env state next result bound run notType ok
  have dynamic : oracleEvalBody (F := F) compiler f state.clock := by
    intro body env' called last inner smaller bodyRun bodyNotType bodyOk
    exact clockIH called.clock (by omega) [body] env' called last inner (Nat.le_refl _)
      bodyRun bodyNotType bodyOk
  cases e with
  | var index => exact oracleEval_var compiler f limit index env state next result bound run notType ok
  | force location index => exact oracleEval_force compiler f location index env state next result dynamic run notType ok
  | ifThenElse cond yes no =>
    exact oracleEval_if compiler f limit cond yes no (structuralIH [cond] (by simp_wf; omega))
      (structuralIH [yes] (by simp_wf; omega)) (structuralIH [no] (by simp_wf; omega))
      env state next result bound run notType ok
  | «let» bindings body =>
    exact oracleEval_let compiler f limit bindings body (structuralIH bindings (by simp_wf; omega))
      (structuralIH [body] (by simp_wf; omega)) env state next result bound run notType ok
  | raise body =>
    exact oracleEval_raise compiler f limit body (structuralIH [body] (by simp_wf))
      env state next result bound run notType ok
  | tick body =>
    exact oracleEval_tick compiler f limit body (structuralIH [body] (by simp_wf))
      env state next result bound run notType ok
  | call ticks dest args handler =>
    exact oracleEval_call compiler f limit ticks dest args handler env state next result bound
      (structuralIH args (by simp_wf; omega)) dynamic run notType ok
  | op operation args =>
    exact oracleEval_op compiler f limit operation args (structuralIH args (by simp_wf; omega))
      env state next result bound run notType ok
  | letCall rets ticks dest args body =>
    exact oracleEval_letCall compiler f limit rets ticks dest args body env state next result bound
      (structuralIH args (by simp_wf; omega)) dynamic run notType ok
  | «return» args =>
    exact oracleEval_return compiler f limit args (structuralIH args (by simp_wf; omega))
      env state next result bound run notType ok

/-- All expression-list cases reduce to singleton cases at the same clock
bound. -/
theorem oracleEval_list_of_singletons {C D F : Type} (compiler : Compiler D) (f : C → D)
    (limit : Nat) (xs : List Bvi.Exp)
    (structuralIH : ∀ ys, sizeOf ys < sizeOf xs → oracleEvalThrough (F := F) compiler f limit ys)
    (singletonStep : ∀ e, xs = [e] →
      (∀ ys, sizeOf ys < sizeOf [e] → oracleEvalThrough (F := F) compiler f limit ys) →
      oracleEvalThrough (F := F) compiler f limit [e]) :
    oracleEvalThrough (F := F) compiler f limit xs := by
  cases xs with
  | nil => exact oracleEval_nil compiler f limit
  | cons first tail =>
    cases tail with
    | nil => exact singletonStep first rfl structuralIH
    | cons second rest =>
      have positive : 0 < sizeOf second := by cases second <;> simp_wf <;> omega
      exact oracleEval_cons compiler f limit first second rest (structuralIH [first] (by simp_wf; omega))
        (structuralIH (second :: rest) (by simp_wf; omega))

/-- Every BVI evaluation whose result is not a type error commutes with
oracle adjustment and preserves callback agreement. This source-shaped
simulation remains untagged pending BVI evaluator and carrier review. -/
theorem oracleEvalThrough_all {C D F : Type} (compiler : Compiler D) (f : C → D) :
    ∀ limit xs, oracleEvalThrough (F := F) compiler f limit xs := by
  apply oracleEvalThrough_of_step
  intro limit xs structuralIH clockIH
  apply oracleEval_list_of_singletons compiler f limit xs structuralIH
  intro e _ smaller
  exact oracleEval_singleton compiler f limit e smaller clockIH

/-- Unbounded form of the oracle-adjustment evaluator simulation. -/
theorem evaluate_adjustOracle {C D F : Type} (compiler : Compiler D) (f : C → D)
    (xs : List Bvi.Exp) (env : List Value) (state next : BviState C F) (result : BviResult)
    (run : evaluate xs env state = (result, next)) (notType : result ≠ .err (.abort .typeError))
    (ok : adjustOracleOk compiler f state) :
    evaluate xs env (adjustOracle compiler f state) = (result, adjustOracle compiler f next) ∧
      adjustOracleOk compiler f next :=
  oracleEvalThrough_all compiler f state.clock xs env state next result (Nat.le_refl _) run notType ok

end Flapjack.Compiler.Backend.BviProps
