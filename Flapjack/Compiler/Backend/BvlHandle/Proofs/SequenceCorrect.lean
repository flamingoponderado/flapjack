module

public import Flapjack.Compiler.Backend.BvlHandle.Proofs.ExpressionCorrect
public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateExpandEnv

@[expose] public section


/-! Preservation for the handler compiler's sequence splitting. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.BvlSem

namespace SequenceCorrectCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
    (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end SequenceCorrectCarrier

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
    have compiled := compileExpression_correct expression [] state result next 0 limit ⟨run, safe', rfl⟩
    simp only [evaluateTuple, compileExp] at compiled
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

/-- The source sequence compiler preserves a closed evaluation followed by
the original optional-continuation behavior. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "compile_seqs_correct"
  (fmap_as_finite_support := [refs])]
theorem compileSeqs_correct {C F : Type} (l : Nat) (x : Bvl.Exp) (acc : Option Bvl.Exp)
    (s1 s2 s3 : Flapjack.Compiler.Backend.BvlSem.State C F)
    (res res3 : SemanticPrimitivesHOL.Result (List Value) Value)
    (premises : evaluateTuple ([x], [], s1) = (res, s2) ∧
      (∀ (y : Bvl.Exp) (r : List Value), acc = some y ∧ res = .val r →
        res3 ≠ .err (.abort .typeError) ∧ evaluateTuple ([y], [], s2) = (res3, s3)) ∧
      res ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSeqs l x acc], [], s1) =
      if acc = none then (res, s2) else
        match res with
        | .val _ => (res3, s3)
        | .err _ => (res, s2) := by
  obtain ⟨run, continuation, safe⟩ := premises
  simp only [evaluateTuple] at run continuation ⊢
  have sourceSafe : (evaluate [x] [] s1).1 ≠ .err (.abort .typeError) := by
    simpa [run] using safe
  have contSafe : sequenceContinueSafe (evaluate [x] [] s1) acc := by
    rw [run]
    cases acc with
    | none => cases res <;> simp [sequenceContinueSafe]
    | some y =>
      cases res with
      | err error => simp [sequenceContinueSafe]
      | val values =>
        obtain ⟨safeNext, nextRun⟩ := continuation y values ⟨rfl, rfl⟩
        simpa [sequenceContinueSafe, nextRun] using safeNext
  have simulation := evaluate_compileSeqsWith l x acc s1 sourceSafe contSafe
  rw [run] at simulation
  change evaluate [compileSeqs l x acc] [] s1 = _
  change evaluate [compileSeqs l x acc] [] s1 = sequenceContinue (res, s2) acc at simulation
  rw [simulation]
  cases acc with
  | none => cases res <;> simp [sequenceContinue]
  | some y =>
    cases res with
    | err error => simp [sequenceContinue]
    | val values =>
      obtain ⟨_, nextRun⟩ := continuation y values ⟨rfl, rfl⟩
      simpa [sequenceContinue] using nextRun

/-- The source handler entry point preserves every non-type-error evaluation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "compile_any_correct"
  (fmap_as_finite_support := [refs])]
theorem compileAny_correct {C F : Type} (x : Bvl.Exp) (env : List Value)
    (s1 : Flapjack.Compiler.Backend.BvlSem.State C F)
    (res : SemanticPrimitivesHOL.Result (List Value) Value)
    (s2 : Flapjack.Compiler.Backend.BvlSem.State C F) (k : Nat) (splitSeq : Bool) (l : Nat)
    (premises : evaluateTuple ([x], env, s1) = (res, s2) ∧
      res ≠ .err (.abort .typeError) ∧ k = env.length) :
    evaluateTuple ([compileAny splitSeq l k x], env, s1) = (res, s2) := by
  rcases premises with ⟨run, safe, rfl⟩
  cases env with
  | nil =>
    cases splitSeq with
    | false =>
      simpa [compileAny, compileExp, evaluateTuple] using
        compileExpression_correct x [] s1 res s2 0 l ⟨run, safe, rfl⟩
    | true =>
      simpa [compileAny] using
        compileSeqs_correct l x none s1 s2 s2 res res ⟨run, by simp, safe⟩
  | cons first rest =>
    simpa [compileAny, compileExp, evaluateTuple] using
      compileExpression_correct x (first :: rest) s1 res s2 (first :: rest).length l ⟨run, safe, rfl⟩

end Flapjack.Compiler.Backend.BvlHandle.Proofs
