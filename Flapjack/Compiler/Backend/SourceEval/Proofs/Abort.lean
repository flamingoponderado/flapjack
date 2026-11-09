import Flapjack.SemanticPrimitivesHOL

/-! Abort classification for source-evaluator simulations. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL

/-- Whether an evaluation result aborts. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "abort_def"]
def abort {α β : Type} (result : Result α β) : Prop :=
  match result with
  | .err (.abort _) => True
  | _ => False

/-- Abort classification for all three result forms. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "abort_simps"]
theorem abort_simps {α β γ δ ε ζ : Type} (a : Abort) (e : δ) (v : ε) :
    (abort (.err (.abort a) : Result α β) ↔ True) ∧
    (abort (.err (.raise e) : Result γ δ) ↔ False) ∧
    (abort (.val v : Result ε ζ) ↔ False) := by
  simp [abort]

/-- A non-aborting result is a value or a raised exception. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "abort_imp_intro"]
theorem abort_imp_intro {α β : Type} (x : Result α β) (P : Prop)
    (premises : (∀ v, x = .val v → P) ∧ (∀ e, x = .err (.raise e) → P)) :
    ¬ abort x → P := by
  cases x with
  | val v => exact fun _ => premises.1 v rfl
  | err e =>
    cases e with
    | raise v => exact fun _ => premises.2 v rfl
    | abort a => simp [abort]

end Flapjack.Compiler.Backend.SourceEval.Proofs
