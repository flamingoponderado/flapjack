import Flapjack.Compiler.Backend.BvlHandle.Proofs.LetLetEvaluate

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

end Flapjack.Compiler.Backend.BvlHandle.Proofs
