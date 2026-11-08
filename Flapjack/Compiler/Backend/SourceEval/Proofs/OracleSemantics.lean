import Flapjack.Compiler.Backend.SourceEval.Proofs.PutOracleClock

/-! Observational program semantics under compiler oracle installation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.AstHOL
open Flapjack.EvaluateHOL Flapjack.NamespaceHOL Flapjack.SemanticsHOL

/-- An installed compiler oracle's behavior is a behavior of the original
non-failing program. The evaluator inherits the rational-cut real-number
assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "oracle_semantics_prog"]
theorem oracle_semantics_prog {Config F : Type} (s : State F) (env : SemEnv Value) (decs : List Dec)
    (ci : CompilerInstance Config) (oracle : EvalOracleFun) (outcome : HolBehaviour)
    (premises : ¬ semanticsProg s env decs .fail ∧
      semanticsProg { s with evalState := putOracle ci oracle } env decs outcome ∧
      precondEvalState oracle ci s env decs ∧ s.refs = [] ∧
      nsAll (fun _ value => concreteValue value = true) env.v) :
    semanticsProg s env decs outcome := by
  obtain ⟨noFail, target, precond, emptyRefs, concrete⟩ := premises
  have clocked : ∀ k, ∃ ffi result result',
      evaluateProgWithClock s env k decs = (ffi, result) ∧
      evaluateProgWithClock { s with evalState := putOracle ci oracle } env k decs = (ffi, result') ∧
      resultRel (fun _ _ => True) (fun _ _ => True) result result' := by
    intro k
    cases sourceRun : evaluateProgWithClock s env k decs with
    | mk ffi result =>
      have safe : result ≠ .err (.abort .typeError) := by
        intro bad
        apply noFail
        change ∃ clock, (evaluateProgWithClock s env clock decs).2 = .err (.abort .typeError)
        exact ⟨k, by simpa [sourceRun] using bad⟩
      obtain ⟨result', targetRun, related⟩ := evaluate_prog_with_clock_put_oracle oracle ci s env decs k ffi result
        ⟨precond, sourceRun, safe, emptyRefs, concrete, noFail⟩
      exact ⟨ffi, result, result', rfl, targetRun, related⟩
  have ffiEqual : ∀ k,
      (evaluateProgWithClock s env k decs).1 =
        (evaluateProgWithClock { s with evalState := putOracle ci oracle } env k decs).1 := by
    intro k
    obtain ⟨ffi, result, result', sourceRun, targetRun, _⟩ := clocked k
    simp [sourceRun, targetRun]
  cases outcome with
  | fail =>
    change ∃ k, (evaluateProgWithClock { s with evalState := putOracle ci oracle } env k decs).2 =
      .err (.abort .typeError) at target
    obtain ⟨clock, bad⟩ := target
    obtain ⟨ffi, result, result', sourceRun, targetRun, related⟩ := clocked clock
    rw [targetRun] at bad
    dsimp only at bad
    subst result'
    have sourceBad : result = .err (.abort .typeError) := by
      cases result with
      | val _ => cases related
      | err error =>
        cases error with
        | raise _ => cases related
        | abort reason =>
          have eq : reason = .typeError := by simpa [resultRel, excRel] using related
          subst reason
          rfl
    exact (noFail ⟨clock, by simpa [sourceRun] using sourceBad⟩).elim
  | diverge trace =>
    change (∀ clock, ∃ ffi, evaluateProgWithClock s env clock decs = (ffi, .err (.abort .timeoutError))) ∧ _
    change (∀ clock, ∃ ffi, evaluateProgWithClock { s with evalState := putOracle ci oracle } env clock decs =
      (ffi, .err (.abort .timeoutError))) ∧ _ at target
    constructor
    · intro clock
      obtain ⟨ffi, result, result', sourceRun, targetRun, related⟩ := clocked clock
      obtain ⟨ffi', timeout⟩ := target.1 clock
      rw [targetRun] at timeout
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj timeout
      cases result with
      | val _ => cases related
      | err error =>
        cases error with
        | raise _ => cases related
        | abort reason =>
          have eq : reason = .timeoutError := by simpa [resultRel, excRel] using related
          subst reason
          exact ⟨ffi, sourceRun⟩
    · simpa only [ffiEqual] using target.2
  | terminate outcome events =>
    change ∃ clock ffi result, _ at target ⊢
    obtain ⟨clock, ffi', targetResult, targetRun', observation, eventsEq, targetSafe⟩ := target
    obtain ⟨ffi, result, result', sourceRun, targetRun, related⟩ := clocked clock
    rw [targetRun] at targetRun'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj targetRun'
    refine ⟨clock, ffi, result, sourceRun, ?_, eventsEq, ?_⟩
    · cases result with
      | val value =>
        cases result' with
        | val other => simpa using observation
        | err error => cases related
      | err error =>
        cases result' with
        | val other => cases related
        | err other =>
          cases error <;> cases other <;> simp_all [resultRel, excRel]
    · intro bad
      apply noFail
      change ∃ k, (evaluateProgWithClock s env k decs).2 = .err (.abort .typeError)
      exact ⟨clock, by simpa [sourceRun] using bad⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs
