import Flapjack.Compiler.Backend.BvlHandle.Proofs.ExpressionCorrect
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateExpandEnv

/-! Preservation for the handler compiler's sequence splitting. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.BvlSem

/-- A source sequence runs its second expression after a successful first
expression and returns that second expression's result. -/
theorem evaluate_sourceSequence {C F : Type} (first second : Bvl.Exp)
    (env : List Value) (state : State C F) :
    evaluate [.let [first, second] (.var 1)] env state =
      match evaluate [first] env state with
      | (.err error, next) => (.err error, next)
      | (.val _, next) => evaluate [second] env next := by
  have cons := BvlProps.evaluateCons first [second] env state
  simp only [evaluateTuple] at cons
  rw [evaluate, fixClock_evaluate, cons]
  cases firstRun : evaluate [first] env state with
  | mk firstResult next =>
    cases firstResult with
    | err error => rfl
    | val firstValues =>
      cases secondRun : evaluate [second] env next with
      | mk secondResult last =>
        cases secondResult with
        | err error => simp [secondRun]
        | val secondValues =>
          obtain ⟨value, rfl⟩ := BvlProps.evaluateSing second env next secondValues last secondRun
          simp [secondRun, evaluate, Flapjack.holHd]

/-- Outcome of running an optional continuation after a successful result. -/
noncomputable def sequenceContinue {C F : Type} (result : EvalResult C F) (acc : Option Bvl.Exp) : EvalResult C F :=
  match result, acc with
  | (.val _, next), some rest => evaluate [rest] [] next
  | _, _ => result

/-- The optional continuation must be type-safe when it is reached. -/
def sequenceContinueSafe {C F : Type} (result : EvalResult C F) (acc : Option Bvl.Exp) : Prop :=
  match result, acc with
  | (.val _, next), some rest => (evaluate [rest] [] next).1 ≠ .err (.abort .typeError)
  | _, _ => True

/-- A safe result followed by a safe continuation remains type-safe. -/
theorem sequenceContinue_safe {C F : Type} (result : EvalResult C F) (acc : Option Bvl.Exp)
    (safe : result.1 ≠ .err (.abort .typeError)) (contSafe : sequenceContinueSafe result acc) :
    (sequenceContinue result acc).1 ≠ .err (.abort .typeError) := by
  cases result with
  | mk result next => cases result <;> cases acc <;> simp_all [sequenceContinue, sequenceContinueSafe]

/-- The leaf form emitted when an expression is not a source sequence. -/
def sequenceLeaf (limit : Nat) (expression : Bvl.Exp) : Option Bvl.Exp → Bvl.Exp
  | none => compileExpression limit 0 expression
  | some rest => .let [compileExpression limit 0 expression] (.let [] (.let [] rest))

/-- A compiled expression followed by a safe closed continuation behaves
like the original expression followed by that continuation. -/
theorem evaluate_compiledSequenceLeaf {C F : Type} (limit : Nat) (expression : Bvl.Exp)
    (acc : Option Bvl.Exp) (state : State C F)
    (safe : (evaluate [expression] [] state).1 ≠ .err (.abort .typeError))
    (contSafe : sequenceContinueSafe (evaluate [expression] [] state) acc) :
    evaluate [sequenceLeaf limit expression acc] [] state =
      sequenceContinue (evaluate [expression] [] state) acc := by
  cases run : evaluate [expression] [] state with
  | mk result next =>
    have safe' : result ≠ .err (.abort .typeError) := by simpa [run] using safe
    have compiled := evaluate_compileExpression limit expression [] state next result run safe'
    simp only [List.length_nil] at compiled
    cases acc with
    | none => simpa [sequenceLeaf, sequenceContinue, run] using compiled
    | some rest =>
      simp only [sequenceLeaf]
      cases result with
      | err error =>
        rw [evaluate, fixClock_evaluate, compiled]
        simp [sequenceContinue]
      | val values =>
        have restSafe : (evaluate [rest] [] next).1 ≠ .err (.abort .typeError) := by
          simpa [sequenceContinueSafe, run] using contSafe
        have expanded := BvlProps.evaluateExpandEnv [rest] [] next values restSafe
        simp only [evaluateTuple, List.nil_append] at expanded
        rw [evaluate, fixClock_evaluate, compiled]
        simp only [evaluate, fixClock]
        simpa [sequenceContinue, run] using expanded

/-- Sequence splitting preserves a safe closed evaluation followed by any
safe optional continuation. This theorem is untagged pending source review
of the underlying BVL evaluator and environment-expansion theorem. -/
theorem evaluate_compileSeqsWith {C F : Type} (limit : Nat) (expression : Bvl.Exp)
    (acc : Option Bvl.Exp) (state : State C F)
    (safe : (evaluate [expression] [] state).1 ≠ .err (.abort .typeError))
    (contSafe : sequenceContinueSafe (evaluate [expression] [] state) acc) :
    evaluate [compileSeqsWith (fun l e => compileExpression l 0 e) limit expression acc] [] state =
      sequenceContinue (evaluate [expression] [] state) acc := by
  by_cases shape : ∃ first second, expression = .let [first, second] (.var 1)
  · obtain ⟨first, second, rfl⟩ := shape
    cases firstRun : evaluate [first] [] state with
    | mk result next =>
      cases result with
      | err error =>
        have firstSafe : (evaluate [first] [] state).1 ≠ .err (.abort .typeError) := by
          simpa [evaluate_sourceSequence, firstRun] using safe
        have firstContSafe : sequenceContinueSafe (evaluate [first] [] state)
            (some (compileSeqsWith (fun l e => compileExpression l 0 e) limit second acc)) := by
          simp [sequenceContinueSafe, firstRun]
        have firstCorrect := evaluate_compileSeqsWith limit first
          (some (compileSeqsWith (fun l e => compileExpression l 0 e) limit second acc))
          state firstSafe firstContSafe
        simpa [compileSeqsWith, evaluate_sourceSequence, firstRun, sequenceContinue] using firstCorrect
      | val values =>
        have firstSafe : (evaluate [first] [] state).1 ≠ .err (.abort .typeError) := by simp [firstRun]
        have secondSafe : (evaluate [second] [] next).1 ≠ .err (.abort .typeError) := by
          simpa [evaluate_sourceSequence, firstRun] using safe
        have secondContSafe : sequenceContinueSafe (evaluate [second] [] next) acc := by
          simpa [evaluate_sourceSequence, firstRun] using contSafe
        have secondCorrect := evaluate_compileSeqsWith limit second acc next secondSafe secondContSafe
        have secondResultSafe := sequenceContinue_safe (evaluate [second] [] next) acc secondSafe secondContSafe
        have firstContSafe : sequenceContinueSafe (evaluate [first] [] state)
            (some (compileSeqsWith (fun l e => compileExpression l 0 e) limit second acc)) := by
          simpa [sequenceContinueSafe, firstRun, secondCorrect] using secondResultSafe
        have firstCorrect := evaluate_compileSeqsWith limit first
          (some (compileSeqsWith (fun l e => compileExpression l 0 e) limit second acc))
          state firstSafe firstContSafe
        simpa [compileSeqsWith, evaluate_sourceSequence, firstRun, sequenceContinue, secondCorrect] using firstCorrect
  · have notShape : ∀ first second, expression = .let [first, second] (.var 1) → False := by
      intro first second equal
      exact shape ⟨first, second, equal⟩
    cases acc with
    | none =>
      rw [compileSeqsWith.eq_2 _ limit expression notShape]
      exact evaluate_compiledSequenceLeaf limit expression none state safe contSafe
    | some rest =>
      rw [compileSeqsWith.eq_3 _ limit expression rest notShape]
      exact evaluate_compiledSequenceLeaf limit expression (some rest) state safe contSafe
termination_by sizeOf expression

/-- The executed handler entry point preserves non-type-error expression
evaluation with sequence splitting either enabled or disabled. Untagged
pending review of the BVL evaluator and its HOL carrier correspondence. -/
theorem evaluate_compileAnyFuel {C F : Type} (fuel : Nat) (splitSeq : Bool) (limit : Nat)
    (expression : Bvl.Exp) (env : List Value) (state final : State C F)
    (result : SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluate [expression] env state = (result, final))
    (notType : result ≠ .err (.abort .typeError)) :
    ∃ output, compileAnyFuel fuel splitSeq limit env.length expression = some output ∧
      evaluate [output] env state = (result, final) := by
  cases env with
  | nil =>
    cases splitSeq with
    | false => exact evaluate_compileAnyFuel_noSplit fuel limit expression [] state final result run notType
    | true =>
      refine ⟨compileSeqsWith (fun l e => compileExpression l 0 e) limit expression none, ?_, ?_⟩
      · simpa using compileAnyFuel_eq_source fuel true limit 0 expression
      · have safe : (evaluate [expression] [] state).1 ≠ .err (.abort .typeError) := by simp [run, notType]
        have contSafe : sequenceContinueSafe (evaluate [expression] [] state) none := by
          cases eval : evaluate [expression] [] state with
          | mk result next => cases result <;> simp [sequenceContinueSafe]
        have correct := evaluate_compileSeqsWith limit expression none state safe contSafe
        simpa [sequenceContinue, run] using correct
  | cons first rest =>
    refine ⟨compileExpression limit (first :: rest).length expression, ?_,
      evaluate_compileExpression limit expression (first :: rest) state final result run notType⟩
    simpa using compileAnyFuel_eq_source fuel splitSeq limit (first :: rest).length expression

end Flapjack.Compiler.Backend.BvlHandle.Proofs
