import Flapjack.Compiler.Backend.BvlHandle.Proofs.LetLetEvaluate
import Flapjack.Compiler.Backend.BvlHandle.Proofs.CanRaise

/-! Compositional cases of the BVL handler compiler simulation. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.DbVars
open Flapjack.Compiler.Backend.BvlSem

/-- The source-shaped simulation and no-raise guarantee for a compiled
singleton. This is untagged infrastructure for assembling the HOL theorem;
the evaluator and indexed environment relation still require source review. -/
def compileSingCorrect (limit : Nat) (expression : Bvl.Exp) : Prop :=
  ∀ (C F : Type) (source target extra : List Value) (state : State C F),
    envRel (compileSing limit source.length expression).2.1 source target →
    (evaluate [expression] source state).1 ≠ .err (.abort .typeError) →
    evaluate [(compileSing limit source.length expression).1] (target ++ extra) state =
      evaluate [expression] source state ∧
    ((compileSing limit source.length expression).2.2.2 = true →
      ∀ value, (evaluate [expression] source state).1 ≠ .err (.raise value))

/-- The corresponding simulation invariant for an expression list. -/
def compileListCorrect (limit : Nat) (expressions : List Bvl.Exp) : Prop :=
  ∀ (C F : Type) (source target extra : List Value) (state : State C F),
    envRel (compileList limit source.length expressions).2.1 source target →
    (evaluate expressions source state).1 ≠ .err (.abort .typeError) →
    evaluate (compileList limit source.length expressions).1 (target ++ extra) state =
      evaluate expressions source state ∧
    ((compileList limit source.length expressions).2.2.2 = true →
      ∀ value, (evaluate expressions source state).1 ≠ .err (.raise value))

/-- Compiling an empty expression list preserves evaluation. -/
theorem compileListCorrect_nil (limit : Nat) : compileListCorrect limit [] := by
  intro C F source target extra state _ _
  simp [compileList, evaluate]

/-- Variable compilation preserves evaluation and never raises. -/
theorem compileSingCorrect_var (limit index : Nat) : compileSingCorrect limit (.var index) := by
  intro C F source target extra state related notType
  refine ⟨evaluate_compileSing_var limit index source target extra state related notType, ?_⟩
  intro _ value
  simp only [evaluate]
  cases source[index]? <;> simp

/-- Force compilation preserves evaluation; its no-raise flag can only be
true for the out-of-range case, which is excluded by the source premise. -/
theorem compileSingCorrect_force (limit location index : Nat) :
    compileSingCorrect limit (.force location index) := by
  intro C F source target extra state related notType
  refine ⟨evaluate_compileSing_force limit location index source target extra state related notType, ?_⟩
  intro noRaise value
  by_cases bound : index < source.length
  · simp [compileSing, bound] at noRaise
  · have missing : source[index]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    simp [evaluate, missing] at notType

/-- A tick either times out without raising or inherits both guarantees
from its body at the decremented clock. -/
theorem compileSingCorrect_tick (limit : Nat) (body : Bvl.Exp)
    (ih : compileSingCorrect limit body) : compileSingCorrect limit (.tick body) := by
  intro C F source target extra state related notType
  simp only [compileSing] at related ⊢
  by_cases zeroClock : state.clock = 0
  · simp [evaluate, zeroClock]
  · have sourceSafe : (evaluate [body] source (decClock 1 state)).1 ≠ .err (.abort .typeError) := by
      simpa [evaluate, zeroClock] using notType
    obtain ⟨same, noRaise⟩ := ih C F source target extra (decClock 1 state) related sourceSafe
    simp only [evaluate, zeroClock, ↓reduceIte]
    exact ⟨same, noRaise⟩

/-- Raising an evaluated value uses the size-cut simulation and always
clears the compiler's no-raise flag. -/
theorem compileSingCorrect_raise (limit : Nat) (body : Bvl.Exp)
    (ih : compileSingCorrect limit body) : compileSingCorrect limit (.raise body) := by
  intro C F source target extra state related notType
  generalize compiledEq : compileSing limit source.length body = data
  obtain ⟨compiled, live, size, noRaise⟩ := data
  have sourceSafe : (evaluate [body] source state).1 ≠ .err (.abort .typeError) := by
    cases run : evaluate [body] source state with
    | mk result next =>
      cases result with
      | err error => simpa [evaluate, run] using notType
      | val values => simp
  have compiledBody : ∀ env suffix, envRel live source env →
      evaluate [compiled] (env ++ suffix) state = evaluate [body] source state := by
    intro env suffix rel
    have correct := ih C F source env suffix state (by simpa [compiledEq] using rel) sourceSafe
    simpa [compiledEq] using correct.1
  simp only [compileSing, compiledEq] at related ⊢
  constructor
  · apply evaluate_optionalLetLetSing live (.raise compiled) (size + 1) limit false
      source target extra state (evaluate [.raise body] source state) ?_ related
    intro env suffix rel
    simp only [evaluate, compiledBody env suffix rel]
  · simp only [optionalLetLetSing]
    split <;> simp

/-- The list case composes the head and tail simulations in evaluation
order and combines their no-raise guarantees. -/
theorem compileListCorrect_cons (limit : Nat) (head : Bvl.Exp) (tail : List Bvl.Exp)
    (headIH : compileSingCorrect limit head) (tailIH : compileListCorrect limit tail) :
    compileListCorrect limit (head :: tail) := by
  intro C F source target extra state related notType
  generalize headEq : compileSing limit source.length head = headData
  obtain ⟨compiledHead, headLive, headSize, headFlag⟩ := headData
  generalize tailEq : compileList limit source.length tail = tailData
  obtain ⟨compiledTail, tailLive, tailSize, tailFlag⟩ := tailData
  simp only [compileList, headEq, tailEq] at related ⊢
  obtain ⟨headRelated, tailRelated⟩ := (envRel_mkUnion headLive tailLive source target).mp related
  have sourceCons := BvlProps.evaluateCons head tail source state
  have targetCons := BvlProps.evaluateCons compiledHead compiledTail (target ++ extra) state
  simp only [evaluateTuple] at sourceCons targetCons
  cases headRun : evaluate [head] source state with
  | mk headResult next =>
    cases headResult with
    | err error =>
      have headSafe : (evaluate [head] source state).1 ≠ .err (.abort .typeError) := by
        simpa [sourceCons, headRun] using notType
      have headCorrect := headIH C F source target extra state (by simpa [headEq] using headRelated) headSafe
      have targetHead : evaluate [compiledHead] (target ++ extra) state = (.err error, next) := by
        simpa [headEq, headRun] using headCorrect.1
      constructor
      · rw [targetCons, targetHead, sourceCons, headRun]
      · intro flags value
        have headFlagTrue : headFlag = true := by cases headFlag <;> cases tailFlag <;> simp_all
        have noRaise := headCorrect.2 (by simpa [headEq] using headFlagTrue) value
        simpa [sourceCons, headRun] using noRaise
    | val values =>
      have headSafe : (evaluate [head] source state).1 ≠ .err (.abort .typeError) := by simp [headRun]
      have headCorrect := headIH C F source target extra state (by simpa [headEq] using headRelated) headSafe
      have targetHead : evaluate [compiledHead] (target ++ extra) state = (.val values, next) := by
        simpa [headEq, headRun] using headCorrect.1
      have tailSafe : (evaluate tail source next).1 ≠ .err (.abort .typeError) := by
        rw [sourceCons, headRun] at notType
        cases tailRun : evaluate tail source next with
        | mk result last => cases result <;> simp_all
      have tailCorrect := tailIH C F source target extra next (by simpa [tailEq] using tailRelated) tailSafe
      have targetTail : evaluate compiledTail (target ++ extra) next = evaluate tail source next := by
        simpa [tailEq] using tailCorrect.1
      constructor
      · simp only [targetCons, targetHead, sourceCons, headRun, targetTail]
      · intro flags value
        have tailFlagTrue : tailFlag = true := by cases headFlag <;> cases tailFlag <;> simp_all
        have noRaise := tailCorrect.2 (by simpa [tailEq] using tailFlagTrue) value
        rw [sourceCons, headRun]
        cases tailRun : evaluate tail source next with
        | mk result last => cases result <;> simp_all

/-- Calls compile their arguments and may themselves raise, so their
no-raise flag is cleared in both size-cut branches. -/
theorem compileSingCorrect_call (limit ticks : Nat) (dest : Option Nat) (args : List Bvl.Exp)
    (ih : compileListCorrect limit args) : compileSingCorrect limit (.call ticks dest args) := by
  intro C F source target extra state related notType
  generalize compiledEq : compileList limit source.length args = data
  obtain ⟨compiled, live, size, noRaise⟩ := data
  have sourceSafe : (evaluate args source state).1 ≠ .err (.abort .typeError) := by
    cases run : evaluate args source state with
    | mk result next =>
      cases result with
      | err error =>
        rw [evaluate, fixClock_evaluate, run] at notType
        simpa [run] using notType
      | val values => simp
  have compiledArgs : ∀ env suffix, envRel live source env →
      evaluate compiled (env ++ suffix) state = evaluate args source state := by
    intro env suffix rel
    have correct := ih C F source env suffix state (by simpa [compiledEq] using rel) sourceSafe
    simpa [compiledEq] using correct.1
  simp only [compileSing, compiledEq] at related ⊢
  constructor
  · apply evaluate_optionalLetLetSing live (.call ticks dest compiled) (size + 1) limit false
      source target extra state (evaluate [.call ticks dest args] source state) ?_ related
    intro env suffix rel
    simp only [evaluate, compiledArgs env suffix rel]
  · simp only [optionalLetLetSing]
    split <;> simp

/-- Non-force operations use the normal optional size cut. -/
theorem compileSing_op_other (limit env : Nat) (op : ClosLang.Op) (args : List Bvl.Exp)
    (notForce : op ≠ .thunkOp .forceThunk) :
    compileSing limit env (.op op args) =
      let (compiled, live, size, noRaise) := compileList limit env args
      optionalLetLetSing (.op op compiled) env live (size + 1) limit noRaise := by
  cases op <;> simp_all [compileSing]

/-- Primitive operations preserve the argument simulation. The special
force-thunk operation is not size-cut and conservatively clears no-raise. -/
theorem compileSingCorrect_op (limit : Nat) (op : ClosLang.Op) (args : List Bvl.Exp)
    (ih : compileListCorrect limit args) : compileSingCorrect limit (.op op args) := by
  intro C F source target extra state related notType
  generalize compiledEq : compileList limit source.length args = data
  obtain ⟨compiled, live, size, noRaise⟩ := data
  have sourceSafe : (evaluate args source state).1 ≠ .err (.abort .typeError) := by
    cases run : evaluate args source state with
    | mk result next =>
      cases result with
      | err error =>
        rw [evaluate, fixClock_evaluate, run] at notType
        simpa [run] using notType
      | val values => simp
  have compiledArgs : ∀ env suffix, envRel live source env →
      evaluate compiled (env ++ suffix) state = evaluate args source state := by
    intro env suffix rel
    have correct := ih C F source env suffix state (by simpa [compiledEq] using rel) sourceSafe
    simpa [compiledEq] using correct.1
  have sourceNoRaise : noRaise = true → ∀ value,
      (evaluate [.op op args] source state).1 ≠ .err (.raise value) := by
    intro flag value
    have argsNoRaise := (ih C F source source [] state (by simpa [compiledEq] using envRel_refl live source)
      sourceSafe).2 (by simpa [compiledEq] using flag) value
    rw [evaluate, fixClock_evaluate]
    cases run : evaluate args source state with
    | mk result next =>
      simp only [run] at argsNoRaise
      cases result with
      | err error => simpa using argsNoRaise
      | val values =>
        cases appRun : doApp op values.reverse next with
        | val pair => cases pair; simp [appRun]
        | err error =>
          simp only [appRun]
          intro equal
          have errEq : error = .raise value := by simpa using equal
          subst error
          exact doApp_not_raise op values.reverse next value appRun
  by_cases force : op = .thunkOp .forceThunk
  · subst op
    simp only [compileSing, compiledEq] at related ⊢
    constructor
    · simp only [evaluate, compiledArgs target extra related]
    · simp
  · rw [compileSing_op_other limit source.length op args force, compiledEq] at related ⊢
    constructor
    · apply evaluate_optionalLetLetSing live (.op op compiled) (size + 1) limit noRaise
        source target extra state (evaluate [.op op args] source state) ?_ related
      intro env suffix rel
      simp only [evaluate, compiledArgs env suffix rel]
    · have flagEq : (optionalLetLetSing (.op op compiled) source.length live (size + 1) limit noRaise).2.2.2 = noRaise := by
        simp only [optionalLetLetSing]
        split <;> rfl
      simpa only [flagEq] using sourceNoRaise

/-- Conditional compilation preserves the selected branch and combines the
no-raise guarantees of the condition and both branches. -/
theorem compileSingCorrect_if (limit : Nat) (condition yes no : Bvl.Exp)
    (conditionIH : compileSingCorrect limit condition)
    (yesIH : compileSingCorrect limit yes) (noIH : compileSingCorrect limit no) :
    compileSingCorrect limit (.ifThenElse condition yes no) := by
  intro C F source target extra state related notType
  generalize conditionEq : compileSing limit source.length condition = conditionData
  obtain ⟨compiledCondition, conditionLive, conditionSize, conditionFlag⟩ := conditionData
  generalize yesEq : compileSing limit source.length yes = yesData
  obtain ⟨compiledYes, yesLive, yesSize, yesFlag⟩ := yesData
  generalize noEq : compileSing limit source.length no = noData
  obtain ⟨compiledNo, noLive, noSize, noFlag⟩ := noData
  let live := mkUnion conditionLive (mkUnion yesLive noLive)
  have core : ∀ env suffix, envRel live source env →
      evaluate [.ifThenElse compiledCondition compiledYes compiledNo] (env ++ suffix) state =
        evaluate [.ifThenElse condition yes no] source state ∧
      ((conditionFlag && yesFlag && noFlag) = true → ∀ value,
        (evaluate [.ifThenElse condition yes no] source state).1 ≠ .err (.raise value)) := by
    intro env suffix rel
    obtain ⟨conditionRel, branchRel⟩ := (envRel_mkUnion conditionLive _ source env).mp rel
    obtain ⟨yesRel, noRel⟩ := (envRel_mkUnion yesLive noLive source env).mp branchRel
    cases conditionRun : evaluate [condition] source state with
    | mk result next =>
      cases result with
      | err error =>
        have safe : (evaluate [condition] source state).1 ≠ .err (.abort .typeError) := by
          rw [evaluate, fixClock_evaluate, conditionRun] at notType
          simpa [conditionRun] using notType
        have correct := conditionIH C F source env suffix state (by simpa [conditionEq] using conditionRel) safe
        have same : evaluate [compiledCondition] (env ++ suffix) state = (.err error, next) := by
          simpa [conditionEq, conditionRun] using correct.1
        constructor
        · rw [evaluate, fixClock_evaluate, evaluate, fixClock_evaluate, same, conditionRun]
        · intro flags value
          have flag : conditionFlag = true := by cases conditionFlag <;> cases yesFlag <;> cases noFlag <;> simp_all
          have safeRaise := correct.2 (by simpa [conditionEq] using flag) value
          rw [evaluate, fixClock_evaluate, conditionRun]
          simpa [conditionRun] using safeRaise
      | val values =>
        obtain ⟨value, rfl⟩ := BvlProps.evaluateSing condition source state values next conditionRun
        have safe : (evaluate [condition] source state).1 ≠ .err (.abort .typeError) := by simp [conditionRun]
        have correct := conditionIH C F source env suffix state (by simpa [conditionEq] using conditionRel) safe
        have same : evaluate [compiledCondition] (env ++ suffix) state = (.val [value], next) := by
          simpa [conditionEq, conditionRun] using correct.1
        cases boolRun : asBool value with
        | none =>
          rw [evaluate, fixClock_evaluate, conditionRun] at notType
          simp [boolRun] at notType
        | some chosen =>
          cases chosen with
          | false =>
            have safeBranch : (evaluate [no] source next).1 ≠ .err (.abort .typeError) := by
              rw [evaluate, fixClock_evaluate, conditionRun] at notType
              simpa [boolRun] using notType
            have branch := noIH C F source env suffix next (by simpa [noEq] using noRel) safeBranch
            have sameBranch : evaluate [compiledNo] (env ++ suffix) next = evaluate [no] source next := by
              simpa [noEq] using branch.1
            constructor
            · rw [evaluate, fixClock_evaluate, evaluate, fixClock_evaluate, same, conditionRun]
              simpa [boolRun] using sameBranch
            · intro flags raised
              have flag : noFlag = true := by cases conditionFlag <;> cases yesFlag <;> cases noFlag <;> simp_all
              have safeRaise := branch.2 (by simpa [noEq] using flag) raised
              rw [evaluate, fixClock_evaluate, conditionRun]
              simpa [boolRun] using safeRaise
          | true =>
            have safeBranch : (evaluate [yes] source next).1 ≠ .err (.abort .typeError) := by
              rw [evaluate, fixClock_evaluate, conditionRun] at notType
              simpa [boolRun] using notType
            have branch := yesIH C F source env suffix next (by simpa [yesEq] using yesRel) safeBranch
            have sameBranch : evaluate [compiledYes] (env ++ suffix) next = evaluate [yes] source next := by
              simpa [yesEq] using branch.1
            constructor
            · rw [evaluate, fixClock_evaluate, evaluate, fixClock_evaluate, same, conditionRun]
              simpa [boolRun] using sameBranch
            · intro flags raised
              have flag : yesFlag = true := by cases conditionFlag <;> cases yesFlag <;> cases noFlag <;> simp_all
              have safeRaise := branch.2 (by simpa [yesEq] using flag) raised
              rw [evaluate, fixClock_evaluate, conditionRun]
              simpa [boolRun] using safeRaise
  simp only [compileSing, conditionEq, yesEq, noEq] at related ⊢
  constructor
  · apply evaluate_optionalLetLetSing live (.ifThenElse compiledCondition compiledYes compiledNo)
      (conditionSize + yesSize + noSize + 1) limit (conditionFlag && yesFlag && noFlag)
      source target extra state (evaluate [.ifThenElse condition yes no] source state) ?_ related
    intro env suffix rel
    exact (core env suffix rel).1
  · have flagEq : (optionalLetLetSing (.ifThenElse compiledCondition compiledYes compiledNo)
        source.length live (conditionSize + yesSize + noSize + 1) limit
        (conditionFlag && yesFlag && noFlag)).2.2.2 = (conditionFlag && yesFlag && noFlag) := by
      simp only [optionalLetLetSing]
      split <;> rfl
    intro flag
    apply (core source [] (envRel_refl live source)).2
    change (optionalLetLetSing (.ifThenElse compiledCondition compiledYes compiledNo)
      source.length live (conditionSize + yesSize + noSize + 1) limit
      (conditionFlag && yesFlag && noFlag)).2.2.2 = true at flag
    rw [flagEq] at flag
    exact flag

/-- The source handler's body cannot encounter a type error if the whole
handler evaluation is type-safe. -/
theorem handle_body_safe {C F : Type} (body handler : Bvl.Exp)
    (source : List Value) (state : State C F)
    (safe : (evaluate [.handle body handler] source state).1 ≠ .err (.abort .typeError)) :
    (evaluate [body] source state).1 ≠ .err (.abort .typeError) := by
  intro bad
  cases run : evaluate [body] source state with
  | mk result next =>
    have resultEq : result = .err (.abort .typeError) := by simpa [run] using bad
    subst result
    rw [evaluate, fixClock_evaluate, run] at safe
    exact safe rfl

/-- A handler can be discarded when its body is known not to raise. -/
theorem compileSingCorrect_handle_noRaise (limit : Nat) (body handler : Bvl.Exp)
    (bodyIH : compileSingCorrect limit body)
    (C F : Type) (source target extra : List Value) (state : State C F)
    (flag : (compileSing limit source.length body).2.2.2 = true)
    (related : envRel (compileSing limit source.length (.handle body handler)).2.1 source target)
    (notType : (evaluate [.handle body handler] source state).1 ≠ .err (.abort .typeError)) :
    evaluate [(compileSing limit source.length (.handle body handler)).1] (target ++ extra) state =
      evaluate [.handle body handler] source state ∧
    ((compileSing limit source.length (.handle body handler)).2.2.2 = true →
      ∀ value, (evaluate [.handle body handler] source state).1 ≠ .err (.raise value)) := by
  generalize compiledEq : compileSing limit source.length body = data
  obtain ⟨compiled, live, size, noRaise⟩ := data
  have flag' : noRaise = true := by simpa [compiledEq] using flag
  simp only [compileSing, compiledEq, flag', ↓reduceIte] at related ⊢
  have safe := handle_body_safe body handler source state notType
  have correct := bodyIH C F source target extra state (by simpa [compiledEq] using related) safe
  have same : evaluate [compiled] (target ++ extra) state = evaluate [body] source state := by
    simpa [compiledEq] using correct.1
  have noRaised : ∀ value, (evaluate [body] source state).1 ≠ .err (.raise value) :=
    correct.2 flag
  have handlerSame : evaluate [.handle body handler] source state = evaluate [body] source state := by
    rw [evaluate, fixClock_evaluate]
    cases run : evaluate [body] source state with
    | mk result next =>
      cases result with
      | val values => simp
      | err error =>
        cases error with
        | abort reason => simp
        | raise value => exact False.elim (noRaised value (by simp [run]))
  constructor
  · exact same.trans handlerSame.symm
  · intro _ value
    rw [handlerSame]
    exact noRaised value

/-- When the body can raise, packing its live variables preserves the body
run, and the handler simulation applies after extending both environments
with the raised value. -/
theorem compileSingCorrect_handle_mayRaise (limit : Nat) (body handler : Bvl.Exp)
    (bodyIH : compileSingCorrect limit body) (handlerIH : compileSingCorrect limit handler)
    (C F : Type) (source target extra : List Value) (state : State C F)
    (flag : (compileSing limit source.length body).2.2.2 = false)
    (related : envRel (compileSing limit source.length (.handle body handler)).2.1 source target)
    (notType : (evaluate [.handle body handler] source state).1 ≠ .err (.abort .typeError)) :
    evaluate [(compileSing limit source.length (.handle body handler)).1] (target ++ extra) state =
      evaluate [.handle body handler] source state ∧
    ((compileSing limit source.length (.handle body handler)).2.2.2 = true →
      ∀ value, (evaluate [.handle body handler] source state).1 ≠ .err (.raise value)) := by
  generalize bodyEq : compileSing limit source.length body = bodyData
  obtain ⟨compiledBody, bodyLive, bodySize, bodyFlag⟩ := bodyData
  have flag' : bodyFlag = false := by simpa [bodyEq] using flag
  generalize handlerEq : compileSing limit (source.length + 1) handler = handlerData
  obtain ⟨compiledHandler, handlerLive, handlerSize, handlerFlag⟩ := handlerData
  simp only [compileSing, bodyEq, flag', Bool.false_eq_true, ↓reduceIte, handlerEq] at related ⊢
  obtain ⟨bodyRel, handlerRel⟩ := (envRel_mkUnion bodyLive (.shift 1 handlerLive) source target).mp related
  have safe := handle_body_safe body handler source state notType
  have bodySimulation : ∀ env suffix, envRel bodyLive source env →
      evaluate [compiledBody] (env ++ suffix) state = evaluate [body] source state := by
    intro env suffix rel
    have correct := bodyIH C F source env suffix state (by simpa [bodyEq] using rel) safe
    simpa [bodyEq] using correct.1
  have packedRun : evaluate [letLet source.length (dbToSet bodyLive) compiledBody]
      (target ++ extra) state = evaluate [body] source state :=
    evaluate_letLet bodyLive compiledBody source target extra state _ bodySimulation bodyRel
  cases bodyRun : evaluate [body] source state with
  | mk result next =>
    cases result with
    | val values =>
      constructor
      · rw [evaluate, fixClock_evaluate, packedRun, evaluate, fixClock_evaluate, bodyRun]
      · intro _ value
        rw [evaluate, fixClock_evaluate, bodyRun]
        simp
    | err error =>
      cases error with
      | abort reason =>
        constructor
        · rw [evaluate, fixClock_evaluate, packedRun, evaluate, fixClock_evaluate, bodyRun]
        · intro _ value
          rw [evaluate, fixClock_evaluate, bodyRun]
          simp
      | raise raised =>
        have handlerSafe : (evaluate [handler] (raised :: source) next).1 ≠ .err (.abort .typeError) := by
          rw [evaluate, fixClock_evaluate, bodyRun] at notType
          exact notType
        have extended : envRel handlerLive (raised :: source) (raised :: target) := by
          simpa using envRel_prepend_shift handlerLive source target [raised] handlerRel
        have handlerCorrect := handlerIH C F (raised :: source) (raised :: target) extra next
          (by simpa [handlerEq, Nat.add_comm] using extended) handlerSafe
        have handlerSame : evaluate [compiledHandler] ((raised :: target) ++ extra) next =
            evaluate [handler] (raised :: source) next := by
          simpa [handlerEq, Nat.add_comm] using handlerCorrect.1
        constructor
        · rw [evaluate, fixClock_evaluate, packedRun, evaluate, fixClock_evaluate, bodyRun]
          exact handlerSame
        · intro flagTrue value
          rw [evaluate, fixClock_evaluate, bodyRun]
          exact handlerCorrect.2 (by simpa [handlerEq, Nat.add_comm] using flagTrue) value

/-- Handler compilation preserves evaluation in both the eliminated-handler
and potentially-raising cases. -/
theorem compileSingCorrect_handle (limit : Nat) (body handler : Bvl.Exp)
    (bodyIH : compileSingCorrect limit body) (handlerIH : compileSingCorrect limit handler) :
    compileSingCorrect limit (.handle body handler) := by
  intro C F source target extra state related notType
  cases flag : (compileSing limit source.length body).2.2.2 with
  | false =>
    exact compileSingCorrect_handle_mayRaise limit body handler bodyIH handlerIH
      C F source target extra state flag related notType
  | true =>
    exact compileSingCorrect_handle_noRaise limit body handler bodyIH
      C F source target extra state flag related notType

/-- Let compilation composes binding evaluation with the body in the
extended environment, accounting for the compiled bindings' exact length. -/
theorem compileSingCorrect_let (limit : Nat) (bindings : List Bvl.Exp) (body : Bvl.Exp)
    (bindingsIH : compileListCorrect limit bindings) (bodyIH : compileSingCorrect limit body) :
    compileSingCorrect limit (.let bindings body) := by
  intro C F source target extra state related notType
  cases bindings with
  | nil =>
    simp only [compileSing, List.isEmpty_nil, ↓reduceIte] at related ⊢
    have safe : (evaluate [body] source state).1 ≠ .err (.abort .typeError) := by
      simpa [evaluate, fixClock] using notType
    have correct := bodyIH C F source target extra state related safe
    simpa [evaluate, fixClock] using correct
  | cons first rest =>
    let bindings := first :: rest
    generalize bindingsEq : compileList limit source.length bindings = bindingsData
    obtain ⟨compiledBindings, bindingsLive, bindingsSize, bindingsFlag⟩ := bindingsData
    generalize bodyEq : compileSing limit (source.length + bindings.length) body = bodyData
    obtain ⟨compiledBody, bodyLive, bodySize, bodyFlag⟩ := bodyData
    have bindingsEq' : compileList limit source.length (first :: rest) =
        (compiledBindings, bindingsLive, bindingsSize, bindingsFlag) := by
      simpa [bindings] using bindingsEq
    have bodyEq' : compileSing limit (source.length + (first :: rest).length) body =
        (compiledBody, bodyLive, bodySize, bodyFlag) := by
      simpa [bindings] using bodyEq
    let live := mkUnion bindingsLive (.shift bindings.length bodyLive)
    have core : ∀ env suffix, envRel live source env →
        evaluate [.let compiledBindings compiledBody] (env ++ suffix) state =
          evaluate [.let bindings body] source state ∧
        ((bindingsFlag && bodyFlag) = true → ∀ value,
          (evaluate [.let bindings body] source state).1 ≠ .err (.raise value)) := by
      intro env suffix rel
      obtain ⟨bindingsRel, bodyRel⟩ :=
        (envRel_mkUnion bindingsLive (.shift bindings.length bodyLive) source env).mp rel
      cases bindingsRun : evaluate bindings source state with
      | mk result next =>
        cases result with
        | err error =>
          have bindingsRun' : evaluate (first :: rest) source state = (.err error, next) := bindingsRun
          have safe : (evaluate bindings source state).1 ≠ .err (.abort .typeError) := by
            rw [evaluate, fixClock_evaluate, bindingsRun] at notType
            simpa [bindingsRun, bindings] using notType
          have correct := bindingsIH C F source env suffix state (by simpa [bindingsEq'] using bindingsRel) (by simpa [bindings] using safe)
          have same : evaluate compiledBindings (env ++ suffix) state = (.err error, next) := by
            simpa [bindingsEq', bindingsRun'] using correct.1
          constructor
          · rw [evaluate, fixClock_evaluate, evaluate, fixClock_evaluate, same, bindingsRun]
          · intro flags value
            have flag : bindingsFlag = true := by cases bindingsFlag <;> cases bodyFlag <;> simp_all
            have safeRaise := correct.2 (by simpa [bindingsEq'] using flag) value
            rw [evaluate, fixClock_evaluate, bindingsRun]
            simpa [bindingsRun'] using safeRaise
        | val values =>
          have bindingsRun' : evaluate (first :: rest) source state = (.val values, next) := bindingsRun
          have safe : (evaluate bindings source state).1 ≠ .err (.abort .typeError) := by simp [bindingsRun]
          have correct := bindingsIH C F source env suffix state (by simpa [bindingsEq'] using bindingsRel) (by simpa [bindings] using safe)
          have same : evaluate compiledBindings (env ++ suffix) state = (.val values, next) := by
            simpa [bindingsEq', bindingsRun'] using correct.1
          have valuesLength : values.length = bindings.length :=
            (BvlProps.evaluateImpLength bindings source state values next bindingsRun).symm
          have bodySafe : (evaluate [body] (values ++ source) next).1 ≠ .err (.abort .typeError) := by
            rw [evaluate, fixClock_evaluate, bindingsRun] at notType
            simpa [bindings] using notType
          have extended : envRel bodyLive (values ++ source) (values ++ env) := by
            apply envRel_prepend_shift bodyLive source env values
            simpa [valuesLength] using bodyRel
          have bodyCompiled : compileSing limit (values ++ source).length body =
              (compiledBody, bodyLive, bodySize, bodyFlag) := by
            simpa [List.length_append, valuesLength, Nat.add_comm] using bodyEq
          have bodyCompiled' : compileSing limit (values.length + source.length) body =
              (compiledBody, bodyLive, bodySize, bodyFlag) := by
            simpa only [List.length_append] using bodyCompiled
          have bodyCorrect := bodyIH C F (values ++ source) (values ++ env) suffix next
            (by simpa only [List.length_append, bodyCompiled'] using extended) bodySafe
          have bodySame : evaluate [compiledBody] ((values ++ env) ++ suffix) next =
              evaluate [body] (values ++ source) next := by
            simpa only [List.length_append, bodyCompiled'] using bodyCorrect.1
          constructor
          · rw [evaluate, fixClock_evaluate, evaluate, fixClock_evaluate, same, bindingsRun]
            simpa [List.append_assoc] using bodySame
          · intro flags value
            have flag : bodyFlag = true := by cases bindingsFlag <;> cases bodyFlag <;> simp_all
            have safeRaise := bodyCorrect.2 (by simpa only [List.length_append, bodyCompiled'] using flag) value
            rw [evaluate, fixClock_evaluate, bindingsRun]
            exact safeRaise
    change envRel (compileSing limit source.length (.let bindings body)).2.1 source target at related
    change evaluate [(compileSing limit source.length (.let bindings body)).1] (target ++ extra) state =
      evaluate [.let bindings body] source state ∧ _
    simp only [compileSing, bindings, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, bindingsEq', bodyEq'] at related ⊢
    change envRel (optionalLetLetSing (.let compiledBindings compiledBody) source.length live
      (bindingsSize + bodySize + 1) limit (bindingsFlag && bodyFlag)).2.1 source target at related
    change evaluate [(optionalLetLetSing (.let compiledBindings compiledBody) source.length live
      (bindingsSize + bodySize + 1) limit (bindingsFlag && bodyFlag)).1] (target ++ extra) state =
      evaluate [.let bindings body] source state ∧ _
    constructor
    · apply evaluate_optionalLetLetSing live (.let compiledBindings compiledBody) (bindingsSize + bodySize + 1)
        limit (bindingsFlag && bodyFlag) source target extra state (evaluate [.let bindings body] source state) ?_ related
      intro env suffix rel
      exact (core env suffix rel).1
    · have flagEq : (optionalLetLetSing (.let compiledBindings compiledBody) source.length live
          (bindingsSize + bodySize + 1) limit (bindingsFlag && bodyFlag)).2.2.2 = (bindingsFlag && bodyFlag) := by
        simp only [optionalLetLetSing]
        split <;> rfl
      intro flag
      apply (core source [] (envRel_refl live source)).2
      rw [flagEq] at flag
      exact flag

mutual
/-- Simulation of every singleton under the handler compiler's live-variable
relation. Untagged pending review of the evaluator and environment relation
against the HOL carriers. -/
theorem compileSingCorrect_all (limit : Nat) (expression : Bvl.Exp) :
    compileSingCorrect limit expression := by
  cases expression with
  | var index => exact compileSingCorrect_var limit index
  | force location index => exact compileSingCorrect_force limit location index
  | tick body => exact compileSingCorrect_tick limit body (compileSingCorrect_all limit body)
  | raise body => exact compileSingCorrect_raise limit body (compileSingCorrect_all limit body)
  | call ticks dest args => exact compileSingCorrect_call limit ticks dest args (compileListCorrect_all limit args)
  | op op args => exact compileSingCorrect_op limit op args (compileListCorrect_all limit args)
  | ifThenElse condition yes no =>
    exact compileSingCorrect_if limit condition yes no (compileSingCorrect_all limit condition)
      (compileSingCorrect_all limit yes) (compileSingCorrect_all limit no)
  | handle body handler =>
    exact compileSingCorrect_handle limit body handler (compileSingCorrect_all limit body)
      (compileSingCorrect_all limit handler)
  | «let» bindings body =>
    exact compileSingCorrect_let limit bindings body (compileListCorrect_all limit bindings)
      (compileSingCorrect_all limit body)
termination_by sizeOf expression

/-- Simulation of every expression list under the handler compiler's
live-variable relation. -/
theorem compileListCorrect_all (limit : Nat) (expressions : List Bvl.Exp) :
    compileListCorrect limit expressions := by
  cases expressions with
  | nil => exact compileListCorrect_nil limit
  | cons head tail =>
    exact compileListCorrect_cons limit head tail (compileSingCorrect_all limit head)
      (compileListCorrect_all limit tail)
termination_by sizeOf expressions
end

end Flapjack.Compiler.Backend.BvlHandle.Proofs
