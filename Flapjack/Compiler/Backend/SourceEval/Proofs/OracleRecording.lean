import Flapjack.Compiler.Backend.SourceEval.Proofs
import Lean.Elab.Tactic.Omega

/-! Recorded-oracle agreement and prefix preservation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "orac_agrees_def"]
def oracleAgrees (oracle : EvalOracleFun) (state : Option EvalState) : Prop :=
  match state with
  | some (.evalOracle s) => ∀ j, j < (s.oracle 0).1.1 → oracle j = s.oracle (j + 1)
  | _ => False

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "orac_extended_wf_def"]
def oracleExtendedWellFormed {α β γ δ : Type} (compiler : α × β × γ → Option (β × δ))
    (oracle : Nat → α × β × γ) : Prop :=
  ∀ i result, compiler (oracle i) = some result → result.1 = (oracle (i + 1)).2.1

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "record_forward_def"]
def recordForward (before after : Option EvalState) : Prop :=
  match before with
  | some (.evalOracle s) => ∃ s', after = some (.evalOracle s') ∧
      (s.oracle 0).1.1 ≤ (s'.oracle 0).1.1 ∧
      ∀ j, 0 < j ∧ j < (s.oracle 0).1.1 + 1 → s'.oracle j = s.oracle j
  | _ => match after with
    | some (.evalOracle _) => False
    | _ => True

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "record_forward_refl"]
theorem recordForward_refl (state : Option EvalState) : recordForward state state := by
  cases state with
  | none => trivial
  | some state =>
    cases state with
    | evalDecs s => trivial
    | evalOracle s => exact ⟨s, rfl, Nat.le_refl _, fun _ _ => rfl⟩

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "record_forward_trans"]
theorem recordForward_trans (first second third : Option EvalState)
    (premises : recordForward first second ∧ recordForward second third) :
    recordForward first third := by
  rcases premises with ⟨left, right⟩
  cases first with
  | none =>
    cases second with
    | none => exact right
    | some s => cases s with
      | evalDecs _ => exact right
      | evalOracle _ => cases left
  | some s =>
    cases s with
    | evalDecs s =>
      cases second with
      | none => exact right
      | some t => cases t with
        | evalDecs _ => exact right
        | evalOracle _ => cases left
    | evalOracle s =>
      obtain ⟨t, rfl, count₁, prefix₁⟩ := left
      obtain ⟨u, rfl, count₂, prefix₂⟩ := right
      refine ⟨u, rfl, Nat.le_trans count₁ count₂, ?_⟩
      intro j hj
      exact (prefix₂ j ⟨hj.1, by omega⟩).trans (prefix₁ j hj)

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "orac_agrees_backward"]
theorem oracleAgrees_backward (oracle : EvalOracleFun) (second first : Option EvalState)
    (premises : oracleAgrees oracle second ∧ recordForward first second) :
    oracleAgrees oracle first := by
  rcases premises with ⟨agrees, forward⟩
  cases first with
  | none =>
    cases second with
    | none => exact agrees
    | some s => cases s with
      | evalDecs _ => exact agrees
      | evalOracle _ => cases forward
  | some s =>
    cases s with
    | evalDecs s =>
      cases second with
      | none => exact agrees
      | some t => cases t with
        | evalDecs _ => exact agrees
        | evalOracle _ => cases forward
    | evalOracle s =>
      obtain ⟨t, rfl, count, savedPrefix⟩ := forward
      intro j hj
      exact (agrees j (by omega)).trans (savedPrefix (j + 1) ⟨by omega, by omega⟩)

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "recorded_orac_wf_step"]
theorem recordedOracleWellFormed_step (compiler : CompilerFun) (oracle : EvalOracleFun)
    (args : CompilerArgs) (nextValue bytesValue wordsValue : Value)
    (premises : recordedOracleWellFormed compiler oracle ∧
      compilerAgrees compiler args (nextValue, bytesValue, wordsValue) ∧
      (0 < (oracle 0).1.1 → args.2.1 = (oracle 0).2.1)) :
    recordedOracleWellFormed compiler (fun j =>
      if j = 0 then (((oracle 0).1.1 + 1, 0), nextValue, [])
      else if j = (oracle 0).1.1 + 1 then args else oracle j) := by
  classical
  obtain ⟨wf, agrees, previous⟩ := premises
  have compiled : ∃ bytes words, compiler args = some (nextValue, bytes, words) := by
    obtain ⟨id, state, decs⟩ := args
    cases compiledEq : compiler (id, state, decs) with
    | none => simp [compilerAgrees, compiledEq] at agrees
    | some triple =>
      obtain ⟨result, bytes, words⟩ := triple
      cases decodedBytes : valueToWord8List bytesValue with
      | none => simp [compilerAgrees, compiledEq, decodedBytes] at agrees
      | some decodedBytes =>
        cases decodedWords : valueToWord64List wordsValue with
        | none => simp [compilerAgrees, compiledEq, decodedBytes, decodedWords] at agrees
        | some decodedWords =>
          simp [compilerAgrees, compiledEq, decodedBytes, decodedWords] at agrees
          exact ⟨bytes, words, by simp [agrees.1]⟩
  obtain ⟨bytes, words, compiled⟩ := compiled
  have ⟨last, middle⟩ := wf
  constructor
  · intro _
    refine ⟨(nextValue, bytes, words), ?_, ?_⟩
    · simpa using compiled
    · simp
  · intro j hj
    have positive : 0 < j := hj.2
    have bound : j < (oracle 0).1.1 + 1 := by simpa using hj.1
    by_cases atLast : j = (oracle 0).1.1
    · subst j
      obtain ⟨result, oldCompiled, oldState⟩ := last positive
      refine ⟨result, ?_, ?_⟩
      · simpa [show (oracle 0).1.1 ≠ 0 by omega] using oldCompiled
      · simpa using (previous positive).trans oldState
    · have below : j < (oracle 0).1.1 := by omega
      obtain ⟨result, oldCompiled, oldState⟩ := middle j ⟨below, positive⟩
      refine ⟨result, ?_, ?_⟩
      · simpa [show j ≠ 0 by omega, show j ≠ (oracle 0).1.1 + 1 by omega] using oldCompiled
      · simpa [show j + 1 ≠ 0 by omega, atLast] using oldState

end Flapjack.Compiler.Backend.SourceEval.Proofs
