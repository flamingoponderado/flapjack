module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.RecordSuffixControl

@[expose] public section

/-! Short-circuit case of the recording-oracle clock suffix theorem. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- The short-circuit case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_Log {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (op : Lop) (first second : AstHOL.Exp)
    (ih : (∀ middle outcome values selection branch, evaluate s env [first] = (middle, outcome) ∧
      outcome = .val values ∧ doLog op (headValue values) second = some selection ∧ selection = .exp branch →
      ExpsSuffixAt ci k middle env [branch]) ∧ ExpsSuffixAt ci k s env [first]) :
    ExpsSuffixAt ci k s env [.log op first second] := by
  obtain ⟨branchIH, firstIH⟩ := ih
  intro s' res ⟨run, recorded, bound⟩
  rw [evaluate, (fixClockEvaluate s env [first] []).1] at run
  cases firstRun : evaluate s env [first] with
  | mk middle result =>
    have firstSuffix := firstIH middle result ⟨firstRun, recorded, bound⟩
    have firstRecorded := (evaluate_is_record_forward ci).1 s env [first] middle result ⟨firstRun, recorded⟩
    cases result with
    | err error =>
      simp only [firstRun] at run
      cases run
      rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
      · left
        refine ⟨bound', ?_⟩
        rw [evaluate, (fixClockEvaluate _ _ [first] []).1, equal]
      · right
        refine ⟨short, ?_, forward⟩
        rw [evaluate, (fixClockEvaluate _ _ [first] []).1, equal]
    | val values =>
      simp only [firstRun] at run
      split at run
      next chosen =>
        simp [typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
        · left
          refine ⟨bound', ?_⟩
          rw [evaluate, (fixClockEvaluate _ _ [first] []).1, equal]
          dsimp only
          split <;> simp_all [typeError]
        · right
          refine ⟨short, ?_, forward⟩
          rw [evaluate, (fixClockEvaluate _ _ [first] []).1, equal]
      next value chosen =>
        cases run
        rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
        · left
          refine ⟨bound', ?_⟩
          rw [evaluate, (fixClockEvaluate _ _ [first] []).1, equal]
          dsimp only
          split <;> simp_all
        · right
          refine ⟨short, ?_, forward⟩
          rw [evaluate, (fixClockEvaluate _ _ [first] []).1, equal]
      next branch chosen =>
        have lastRecorded := (evaluate_is_record_forward ci).1 middle env [branch] s' res ⟨run, firstRecorded.1⟩
        rcases firstSuffix with ⟨midBound, firstEqual⟩ | ⟨short, firstEqual, firstForward⟩
        · have suffix := branchIH middle (.val values) values (.exp branch) branch
            ⟨firstRun, rfl, chosen, rfl⟩ s' res ⟨run, firstRecorded.1, midBound⟩
          rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
          · left
            refine ⟨bound', ?_⟩
            rw [evaluate, (fixClockEvaluate _ _ [first] []).1, firstEqual]
            dsimp only
            split <;> simp_all
          · right
            refine ⟨short, ?_, forward⟩
            rw [evaluate, (fixClockEvaluate _ _ [first] []).1, firstEqual]
            dsimp only
            split <;> simp_all
        · right
          refine ⟨short, ?_, recordForward_trans _ _ _ ⟨firstForward, lastRecorded.2.1⟩⟩
          rw [evaluate, (fixClockEvaluate _ _ [first] []).1, firstEqual]
end Flapjack.Compiler.Backend.SourceEval.Proofs
