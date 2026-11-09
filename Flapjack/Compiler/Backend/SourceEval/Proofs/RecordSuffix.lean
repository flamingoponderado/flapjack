module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.RecordSuffixApp
public import Flapjack.EvaluateHOL.Induction

@[expose] public section

/-! Complete mutual recording-oracle clock suffix for the source evaluator. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- The equality case split used by the recording-oracle proof. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "neq_IMP_to_cases"]
theorem neqImpToCases {α : Type} (x : α) (P : Prop) :
    ∀ y, (x ≠ y → P) → x = y ∨ x ≠ y := by
  intro y _
  exact Classical.em (x = y)

/-- The source proof's clock split, including its original logical premise. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "less_sub_1_cases"]
theorem lessSubOneCases (k clock : Nat) (P : Prop)
    (premises : k ≤ clock ∧ (k ≤ clock - 1 → P)) :
    k = clock ∨ k ≤ clock - 1 := by
  omega



/-- Reducing the source evaluator clock either preserves the result with a
reduced final clock, or times out at a recorded-oracle prefix. The evaluator
inherits the rational-cut real-number assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluate_record_suffix {Config F : Type} (ci : CompilerInstance Config) (k : Nat) :
    (∀ (s : State F) (env : SemEnv Value) (exps : List AstHOL.Exp)
      (s' : State F) (res : Result (List Value) Value),
      evaluate s env exps = (s', res) ∧ isRecord ci s.evalState ∧ k ≤ s.clock →
      let ev := evaluate { s with clock := s.clock - k } env exps
      (k ≤ s'.clock ∧ ev = ({ s' with clock := s'.clock - k }, res)) ∨
        ∃ s'', ev = (s'', .err (.abort .timeoutError)) ∧ recordForward s''.evalState s'.evalState) ∧
    (∀ (s : State F) (env : SemEnv Value) (x : Value) (rows : List (Pat × AstHOL.Exp)) (err : Value)
      (s' : State F) (res : Result (List Value) Value),
      evaluateMatch s env x rows err = (s', res) ∧ isRecord ci s.evalState ∧ k ≤ s.clock →
      let ev := evaluateMatch { s with clock := s.clock - k } env x rows err
      (k ≤ s'.clock ∧ ev = ({ s' with clock := s'.clock - k }, res)) ∨
        ∃ s'', ev = (s'', .err (.abort .timeoutError)) ∧ recordForward s''.evalState s'.evalState) ∧
    (∀ (s : State F) (env : SemEnv Value) (decs : List Dec)
      (s' : State F) (res : Result (SemEnv Value) Value),
      evaluateDecs s env decs = (s', res) ∧ isRecord ci s.evalState ∧ k ≤ s.clock →
      let ev := evaluateDecs { s with clock := s.clock - k } env decs
      (k ≤ s'.clock ∧ ev = ({ s' with clock := s'.clock - k }, res)) ∨
        ∃ s'', ev = (s'', .err (.abort .timeoutError)) ∧ recordForward s''.evalState s'.evalState) := by
  apply fullEvaluateInd (ExpsSuffixAt ci k) (MatchSuffixAt ci k) (DecsSuffixAt ci k)
  exact ⟨evaluateRecordSuffix_ExpsNil ci k, evaluateRecordSuffix_ExpsCons ci k, evaluateRecordSuffix_Lit ci k,
    evaluateRecordSuffix_Raise ci k, evaluateRecordSuffix_Handle ci k, evaluateRecordSuffix_Con ci k,
    evaluateRecordSuffix_Var ci k, evaluateRecordSuffix_Fn ci k, evaluateRecordSuffix_App ci k,
    evaluateRecordSuffix_Log ci k, evaluateRecordSuffix_If ci k, evaluateRecordSuffix_Mat ci k,
    evaluateRecordSuffix_Let ci k, evaluateRecordSuffix_Letrec ci k, evaluateRecordSuffix_Tannot ci k,
    evaluateRecordSuffix_Lannot ci k, evaluateRecordSuffix_MatchNil ci k, evaluateRecordSuffix_MatchCons ci k,
    evaluateRecordSuffix_DecsNil ci k, evaluateRecordSuffix_DecsCons ci k, evaluateRecordSuffix_Dlet ci k,
    evaluateRecordSuffix_Dletrec ci k, evaluateRecordSuffix_Dtype ci k, evaluateRecordSuffix_Dtabbrev ci k,
    evaluateRecordSuffix_Denv ci k, evaluateRecordSuffix_Dexn ci k, evaluateRecordSuffix_Dmod ci k,
    evaluateRecordSuffix_Dlocal ci k⟩

end Flapjack.Compiler.Backend.SourceEval.Proofs
