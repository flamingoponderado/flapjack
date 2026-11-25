module

public import Flapjack.SemanticPrimitivesHOL
public import Flapjack.Compiler.Backend.SourceEval.Proofs

@[expose] public section

/-! backendProofScript.sml: `add_eval_state_def` and `add_eval_state_ffi`, the
optional Eval-mode initial state installed by `compile_correct_eval`. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.SourceEval.Proofs

/-- Exact HOL `backendProof$add_eval_state_def` (`backendProofScript.sml:2910-2914`):
without an Eval instance the state is unchanged, and an instance installs the
initial Eval state built by `mk_init_eval_state`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "add_eval_state_def"]
noncomputable def addEvalState {σ Config : Type} (optEval : Option (CompilerInstance Config))
    (state : State σ) : State σ :=
  match optEval with
  | none => state
  | some ci => { state with evalState := some (mkInitEvalState ci) }

/-- Installing an optional Eval state leaves the FFI unchanged. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "add_eval_state_ffi"]
theorem addEvalState_ffi {σ Config : Type} (optEval : Option (CompilerInstance Config))
    (state : State σ) : (addEvalState optEval state).ffi = state.ffi := by
  cases optEval with
  | none => rfl
  | some ci => rfl

end Flapjack.Compiler.Backend.BackendProof
