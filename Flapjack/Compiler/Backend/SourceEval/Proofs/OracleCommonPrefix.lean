import Flapjack.Compiler.Backend.SourceEval.Proofs.RecordSuffix

/-! Common recorded-oracle prefix for declaration evaluation at different clocks. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.EvaluateHOL

/-- Flapjack proof infrastructure: a recording state and its forward extension
agree on every event in the former's recorded prefix. HOL unfolds the two
relations inline in the common-prefix proof. -/
private theorem recordedPrefix_of_forward {Config : Type} (ci : CompilerInstance Config)
    (first second : Option EvalState) (j : Nat)
    (recorded : isRecord ci first) (forward : recordForward first second)
    (bound : j < ((oracleState first).oracle 0).1.1) :
    (oracleState first).oracle (j + 1) = (oracleState second).oracle (j + 1) := by
  obtain ⟨start, rfl⟩ := isRecord_imp ci first recorded
  obtain ⟨finish, rfl, _, entries⟩ := forward
  simp only [oracleState] at bound ⊢
  exact (entries (j + 1) ⟨by omega, by omega⟩).symm

/-- Declaration evaluations at two clocks agree on their common recorded
oracle prefix. The evaluator inherits the rational-cut real-number assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_decs_clock_record_common_prefix"]
theorem evaluate_decs_clock_record_common_prefix {Config F : Type}
    (s : State F) (env : SemEnv Value) (decs : List Dec) (s' : State F)
    (res : Result (SemEnv Value) Value) (k : Nat) (s'' : State F)
    (res' : Result (SemEnv Value) Value) (ci : CompilerInstance Config) (j : Nat)
    (premises : evaluateDecs s env decs = (s', res) ∧
      evaluateDecs { s with clock := k } env decs = (s'', res') ∧
      isRecord ci s.evalState ∧ j < ((oracleState s'.evalState).oracle 0).1.1 ∧
      j < ((oracleState s''.evalState).oracle 0).1.1) :
    (oracleState s'.evalState).oracle (j + 1) = (oracleState s''.evalState).oracle (j + 1) := by
  obtain ⟨original, changed, recorded, firstBound, secondBound⟩ := premises
  have firstRecorded := ((evaluate_is_record_forward ci).2.2 s env decs s' res ⟨original, recorded⟩).1
  have secondRecorded := ((evaluate_is_record_forward ci).2.2 { s with clock := k } env decs s'' res'
    ⟨changed, recorded⟩).1
  by_cases order : s.clock ≤ k
  · have suffix := (evaluate_record_suffix ci (k - s.clock)).2.2 { s with clock := k } env decs s'' res'
      ⟨changed, recorded, by simp⟩
    have shifted : { { s with clock := k } with clock := k - (k - s.clock) } = s := by
      simp only
      have clockEq : k - (k - s.clock) = s.clock := by omega
      rw [clockEq]
    simp only [shifted, original] at suffix
    rcases suffix with ⟨_, equal⟩ | ⟨short, equal, forward⟩
    · cases equal
      rfl
    · cases equal
      exact recordedPrefix_of_forward ci s'.evalState s''.evalState j firstRecorded forward firstBound
  · have suffix := (evaluate_record_suffix ci (s.clock - k)).2.2 s env decs s' res
      ⟨original, recorded, by omega⟩
    have shifted : { s with clock := s.clock - (s.clock - k) } = { s with clock := k } := by
      have clockEq : s.clock - (s.clock - k) = k := by omega
      rw [clockEq]
    simp only [shifted, changed] at suffix
    rcases suffix with ⟨_, equal⟩ | ⟨short, equal, forward⟩
    · cases equal
      rfl
    · cases equal
      exact (recordedPrefix_of_forward ci s''.evalState s'.evalState j secondRecorded forward secondBound).symm
end Flapjack.Compiler.Backend.SourceEval.Proofs
