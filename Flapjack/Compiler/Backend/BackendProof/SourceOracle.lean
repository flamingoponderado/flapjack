module

public import Flapjack.Compiler.Backend.BackendProof.CakeOrac
public import Flapjack.Compiler.Backend.BackendProof.AddEvalState
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.OracleStep
public import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleRecording

@[expose] public section

set_option autoImplicit false

/-! backendProofScript.sml 3061-3154: the source-level Eval oracle built from
`cake_orac` is well formed for the evaluation compiler instance and satisfies
the source-to-flat oracle step invariant. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendDefs
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.Compiler.Backend.BackendProps

/-- One incremental compilation step's source configuration (Flapjack helper). -/
private theorem compileIncProgs_sourceConf {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (p : (Nat × Nat) × List Dec) :
    (compileIncProgs true asmConf c p).1.sourceConf =
      (SourceToFlat.incCompileProg p.1 c.sourceConf (SourceToSource.compile p.2)).1 := by
  obtain ⟨e, d⟩ := p
  rfl

/-- Exact HOL `step_invs_cake_orac` (`backendProofScript.sml:3127-3154`,
`[local]`). HOL `I` is `id`; the inner quantifier's `st` (a value, shadowing the
oracle state) is `stV`. The decoder payload type `β` carries the `Nonempty`
instance that renders HOL's `THE` inside the reviewed `src_orac_step_invs`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "step_invs_cake_orac"
  (total_function_inhabitants := [β]) (words_as_type_indexed_bitvec)]
theorem stepInvs_cakeOrac {width : Nat} [NeZero width] {β : Type} [Nonempty β]
    (st : EvalOracleState)
    (f : Flapjack.Compiler.Backend.Backend.Config × BackendProgs width →
      (Nat × Nat) × Value × List Dec)
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syn : Nat → (Nat × Nat) × List Dec)
    (decf : Value → Option (SourceToFlat.Config × β)) :
    st.oracle = f ∘ cakeOrac asmConf c' syn id id →
    (∀ (x : Flapjack.Compiler.Backend.Backend.Config × BackendProgs width) (k : Nat)
        (envId : Nat × Nat) (stV : Value) (decs : List Dec),
      x = cakeOrac asmConf c' syn id id k →
      f x = (envId, stV, decs) →
      decs = x.2.sourceProg ∧ envId = x.2.envId ∧
        ∃ dSt : SourceToFlat.Config × β, decf stV = some dSt ∧ dSt.1 = x.1.sourceConf) →
    SourceToFlat.OracleInvariant.srcOracStepInvs (some decf) SourceToSource.compile
      (some (.evalOracle st)) := by
  intro hor H
  have key : ∀ k, ∃ dSt : SourceToFlat.Config × β,
      decf (st.oracle k).2.1 = some dSt ∧
      dSt.1 = (cakeConfigs asmConf c' syn k).sourceConf ∧
      (st.oracle k).2.2 = (syn k).2 ∧ (st.oracle k).1 = (syn k).1 := by
    intro k
    have e : f (cakeOrac asmConf c' syn id id k) =
        ((st.oracle k).1, (st.oracle k).2.1, (st.oracle k).2.2) := by
      rw [hor]; rfl
    obtain ⟨h1, h2, dSt, h3, h4⟩ := H _ k _ _ _ rfl e
    rw [cakeOrac_eq_pair] at h1 h2 h4
    exact ⟨dSt, h3, h4, h1.trans (compileIncProgs_srcEnv asmConf _ (syn k)).2,
      h2.trans (compileIncProgs_srcEnv asmConf _ (syn k)).1⟩
  simp only [SourceToFlat.OracleInvariant.srcOracStepInvs]
  refine ⟨fun k envId stV decs hk => ?_, fun k envId stV decs hk => ?_⟩
  · obtain ⟨dSt, hd, -⟩ := key k
    rw [hk] at hd
    exact ⟨dSt.1, dSt.2, hd⟩
  · obtain ⟨d0, hd0, hs0, hp0, he0⟩ := key k
    obtain ⟨d1, hd1, hs1, -, -⟩ := key (k + 1)
    rw [hk] at hp0 he0
    simp only at hp0 he0
    rw [hp0, he0]
    simp only [hd0, hd1, Flapjack.holThe, hs0, hs1]
    exact compileIncProgs_sourceConf asmConf _ (syn k)

/-- Exact HOL `cake_orac_extended_wf` (`backendProofScript.sml:3061-3079`,
`[local]`). HOL `I` is `id`; the oracle's paired lambda is a
pattern-matching lambda; HOL's free `syntax` (a Lean keyword) is `syn`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_extended_wf"
  (words_as_type_indexed_bitvec)]
theorem cakeOrac_extendedWf {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (ci : CompilerInstance Flapjack.Compiler.Backend.Backend.Config)
    (syn : Nat → (Nat × Nat) × List Dec) :
    compile asmConf c prog = some (b, bm, c') ∧ optEvalConfigWf asmConf c' (some ci) →
      oracleExtendedWellFormed (mkCompilerFunFromCi ci)
        ((fun (x : Flapjack.Compiler.Backend.Backend.Config × (Nat × Nat) × List Dec) =>
            let (cfg, id, ds) := x
            (id, ci.configV cfg, ds)) ∘
          cakeOrac asmConf c' syn id (fun ps => (ps.envId, ps.sourceProg))) := by
  rintro ⟨-, hwf⟩ i result hres
  have hwf' := hwf
  obtain ⟨hfun, -, -⟩ := hwf'
  have hsucc : cakeConfigs asmConf c' syn (i + 1) =
      (compileIncProgs true asmConf (cakeConfigs asmConf c' syn i) (syn i)).1 := rfl
  simp only [Function.comp_apply, cakeOrac_eq_pair] at hres ⊢
  rw [(compileIncProgs_srcEnv asmConf _ (syn i)).1,
    (compileIncProgs_srcEnv asmConf _ (syn i)).2] at hres
  rw [hsucc]
  generalize cakeConfigs asmConf c' syn i = C at hres ⊢
  rcases hsyn : syn i with ⟨e, d⟩
  rw [hsyn] at hres
  simp only [id] at hres ⊢
  unfold mkCompilerFunFromCi at hres
  simp only at hres
  rw [configWf_absConc asmConf c' ci ci.configDom _ hwf] at hres
  split_ifs at hres with hdom
  · rw [hfun] at hres
    unfold compileIncProgsForEval at hres
    simp only [Option.bind_eq_bind, Option.bind_some] at hres
    rcases hc : compileIncProgs true asmConf C (e, d) with ⟨c'', ps⟩
    rw [hc] at hres
    simp only
    cases ht : ps.targetProg with
    | none => simp [ht] at hres
    | some t =>
      obtain ⟨bs, ws⟩ := t
      simp [ht] at hres
      rw [← hres]
  · simp at hres

end Flapjack.Compiler.Backend.BackendProof
