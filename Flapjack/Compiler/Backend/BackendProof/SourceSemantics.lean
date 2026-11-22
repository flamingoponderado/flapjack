module

public import Flapjack.SemanticsProps.Clock
public import Flapjack.SemanticsProps.Determinism
public import Flapjack.Compiler.Backend.SourceToSource.Proofs
public import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleSemantics

@[expose] public section

set_option autoImplicit false

/-! backendProofScript.sml 3156-3201: the source-level semantics lemmas used to
discharge the source-to-source and Eval-oracle steps of
`source_eval_to_flat_semantics`. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.SemanticsHOL Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL
open Flapjack.NamespaceHOL Flapjack.Compiler.Backend.SourceEval.Proofs

/-- If `prog` has a behaviour `x`, then its source-to-source compilation has
the same behaviour (non-failing case). Flapjack-specific helper. -/
private theorem compile_behaviour {σ : Type} (s0 : State σ) (env : SemEnv Value) (prog : List Dec)
    (noFail : ¬ semanticsProg s0 env prog .fail) :
    ∃ x, x ≠ .fail ∧ semanticsProg s0 env prog x ∧
      semanticsProg s0 env (SourceToSource.compile prog) x := by
  obtain ⟨x, hx⟩ := SemanticsProps.semanticsProg_total s0 env prog
  refine ⟨x, ?_, hx, SourceToSource.compile_semantics s0 env prog x ⟨noFail, hx⟩⟩
  rintro rfl
  exact noFail hx

/-- Exact HOL `source_to_source_semantics_prog_equiv`
(`backendProofScript.sml:3156-3163`, `[local]`). HOL's Boolean equation is `↔`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "source_to_source_semantics_prog_equiv"]
theorem sourceToSource_semanticsProg_equiv {σ : Type} (s0 : State σ) (env : SemEnv Value)
    (prog : List Dec) (res : HolBehaviour) :
    ¬ semanticsProg s0 env prog .fail →
      (semanticsProg s0 env (SourceToSource.compile prog) res ↔ semanticsProg s0 env prog res) := by
  intro noFail
  obtain ⟨x, _, hx, hcx⟩ := compile_behaviour s0 env prog noFail
  constructor
  · intro h
    rw [SemanticsProps.semanticsProg_deterministic s0 env _ res x ⟨h, hcx⟩]
    exact hx
  · intro h
    rw [SemanticsProps.semanticsProg_deterministic s0 env _ res x ⟨h, hx⟩]
    exact hcx

/-- Exact HOL `source_to_source_semantics_prog_intro`
(`backendProofScript.sml:3165-3173`, `[local]`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "source_to_source_semantics_prog_intro"]
theorem sourceToSource_semanticsProg_intro {σ : Type} (s0 : State σ) (env : SemEnv Value)
    (prog : List Dec) (res : HolBehaviour) :
    ¬ semanticsProg s0 env prog .fail →
      (¬ semanticsProg s0 env (SourceToSource.compile prog) .fail →
        semanticsProg s0 env (SourceToSource.compile prog) res) →
      semanticsProg s0 env prog res := by
  intro noFail step
  obtain ⟨x, hxf, hx, hcx⟩ := compile_behaviour s0 env prog noFail
  have hc : semanticsProg s0 env (SourceToSource.compile prog) res := step fun hf =>
    hxf (SemanticsProps.semanticsProg_deterministic s0 env _ x .fail ⟨hcx, hf⟩)
  rw [SemanticsProps.semanticsProg_deterministic s0 env _ res x ⟨hc, hcx⟩]
  exact hx

/-- Exact HOL `eval_oracle_semantics_prog_intro`
(`backendProofScript.sml:3175-3185`, `[local]`). HOL `K concrete_v` is the
constant predicate on the value, as in the reviewed `oracle_semantics_prog`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "eval_oracle_semantics_prog_intro"]
theorem evalOracle_semanticsProg_intro {Config σ : Type} (s1 : State σ) (env : SemEnv Value)
    (decs : List Dec) (orac : EvalOracleFun) (res : HolBehaviour) :
    ∀ ci : CompilerInstance Config,
      ¬ semanticsProg s1 env decs .fail ∧
        precondEvalState orac ci s1 env decs ∧ s1.refs = [] ∧
        nsAll (fun _ value => concreteValue value = true) env.v ∧
        (¬ semanticsProg { s1 with evalState := putOracle ci orac } env decs .fail →
          semanticsProg { s1 with evalState := putOracle ci orac } env decs res) →
      semanticsProg s1 env decs res := by
  intro ci ⟨noFail, precond, refs, concrete, step⟩
  have back : ∀ b, semanticsProg { s1 with evalState := putOracle ci orac } env decs b →
      semanticsProg s1 env decs b := fun b hb =>
    oracle_semantics_prog s1 env decs ci orac b ⟨noFail, hb, precond, refs, concrete⟩
  exact back res (step fun hf => noFail (back .fail hf))

/-- Exact HOL `source_to_source_semantics_prog_oracle_intro`
(`backendProofScript.sml:3187-3201`, `[local]`). HOL `I` is `id`; the
compiler-instance carrier is independent of the FFI state. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "source_to_source_semantics_prog_oracle_intro"]
theorem sourceToSource_semanticsProg_oracle_intro {Config σ : Type} (s0 : State σ)
    (env : SemEnv Value) (prog : List Dec) (ev : CompilerInstance Config)
    (sf : CompilerArgs → Nat) (orac : EvalOracleFun) (es : Option EvalState)
    (res : HolBehaviour) :
    ¬ semanticsProg { s0 with evalState := insertGenOracle ev id sf orac es } env prog .fail →
      (¬ semanticsProg
          { s0 with evalState := insertGenOracle ev SourceToSource.compile sf orac es } env prog .fail →
        semanticsProg
          { s0 with evalState := insertGenOracle ev SourceToSource.compile sf orac es } env prog res) →
      semanticsProg { s0 with evalState := insertGenOracle ev id sf orac es } env prog res := by
  intro noFail step
  obtain ⟨x, hx⟩ := SemanticsProps.semanticsProg_total
    { s0 with evalState := insertGenOracle ev id sf orac es } env prog
  have ins : isInsertOracle ev id
      ({ s0 with evalState := insertGenOracle ev id sf orac es } : State σ).evalState :=
    ⟨es, sf, orac, rfl⟩
  have hB := SourceToSource.compile_semantics_oracle ev
    { s0 with evalState := insertGenOracle ev id sf orac es } env prog x id ⟨ins, noFail, hx⟩
  have hB' : semanticsProg
      { s0 with evalState := insertGenOracle ev SourceToSource.compile sf orac es } env prog x := by
    have := adjustOracle_insertGenOracle ev SourceToSource.compile id sf orac es
    simpa only [Function.comp_id, this] using hB
  have hxf : x ≠ .fail := by
    rintro rfl
    exact noFail hx
  have hres := step fun hf =>
    hxf (SemanticsProps.semanticsProg_deterministic _ env prog x .fail ⟨hB', hf⟩)
  rw [SemanticsProps.semanticsProg_deterministic _ env prog res x ⟨hres, hB'⟩]
  exact hx

end Flapjack.Compiler.Backend.BackendProof
