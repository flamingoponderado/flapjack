module

public import Flapjack.SemanticsProps.Clock
public import Flapjack.SemanticsProps.Determinism
public import Mathlib.Data.Set.Basic

@[expose] public section

/-! backendProofScript.sml 4451-4457: facts used by the top-level correctness
theorems. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.SemanticsHOL Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- Exact HOL `semantics_prog_sing` (`backendProofScript.sml:4451-4457`). HOL's
behaviour set `semantics_prog s env prog` is the predicate `semanticsProg`
viewed as a `Set`; `{x}` is the singleton set. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "semantics_prog_sing"]
theorem semanticsProg_sing {σ : Type} (s : State σ) (env : SemEnv Value) (prog : List Dec) :
    ∃ x : HolBehaviour, (semanticsProg s env prog : Set HolBehaviour) = ({x} : Set HolBehaviour) := by
  obtain ⟨x, hx⟩ := SemanticsProps.semanticsProg_total s env prog
  refine ⟨x, Set.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · exact SemanticsProps.semanticsProg_deterministic s env prog y x ⟨hy, hx⟩
  · have hy' : y = x := hy
    subst hy'
    exact hx

end Flapjack.Compiler.Backend.BackendProof
