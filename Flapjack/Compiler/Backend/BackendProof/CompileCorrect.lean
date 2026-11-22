module

public import Flapjack.SemanticsProps.Clock
public import Flapjack.SemanticsProps.Determinism
public import Mathlib.Data.Set.Basic
public import Flapjack.HolArb

@[expose] public section

set_option autoImplicit false

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

/-- `EvalDecsState` is inhabited (Flapjack infrastructure for HOL's
unspecified `the_EvalDecs` completion below; no correctness content). -/
instance : Nonempty EvalDecsState :=
  ⟨{ compiler := fun _ => none, compilerState := .litv (.intLit 0),
     envIdCounter := (0, 0, 0), decodeDecs := fun _ => none }⟩

/-- Exact HOL `the_EvalDecs_def` (`backendProofScript.sml:4482-4484`): the
single clause `the_EvalDecs (EvalDecs x) = x`. HOL leaves the `EvalOracle`
case unspecified; as for the reviewed `the_Litv_*` selectors it is the shared
unspecified value `Flapjack.holArb`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "the_EvalDecs_def"]
noncomputable def theEvalDecs : EvalState → EvalDecsState
  | .evalDecs x => x
  | _ => Flapjack.holArb EvalDecsState

end Flapjack.Compiler.Backend.BackendProof
