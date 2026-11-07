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

end Flapjack.Compiler.Backend.SourceEval.Proofs
