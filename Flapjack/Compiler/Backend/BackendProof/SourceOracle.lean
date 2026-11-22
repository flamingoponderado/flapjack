module

public import Flapjack.Compiler.Backend.BackendProof.CakeOrac
public import Flapjack.Compiler.Backend.BackendProof.AddEvalState
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.OracleStep
public import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleRecording
public import Flapjack.Compiler.Backend.SourceEval.Proofs.GetOracleProps

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

/-- HOL `step_invs_cake_orac` (`backendProofScript.sml:3127-3154`, `[local]`;
capture `step_invs_cake_orac_typed`). HOL `I` is `id`; the inner quantifier's
`st` (a value, shadowing the oracle state) is `stV`. HOL's free decoder payload
type `'b` is `β`; its single `Nonempty β` instance exists only because the
conclusion is the reviewed `srcOracStepInvs` (tagged
`total_function_inhabitants := [C]`) at `C := β`, whose body renders HOL `THE`
on the decoder result by `holThe`. This transitive rendering is the narrow
allow-listed exception for this theorem in `check-hol-refs.py` and the
`StepInvsCakeOracAudit` export audit. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "step_invs_cake_orac"
  (words_as_type_indexed_bitvec) (total_function_inhabitants := [β])]
theorem stepInvs_cakeOrac {width : Nat} [NeZero width] {β : Type} [Nonempty β]
    (st : EvalOracleState)
    (f : Flapjack.Compiler.Backend.Backend.Config × BackendProgs width →
      (Nat × Nat) × Flapjack.SemanticPrimitivesHOL.Value × List Dec)
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syn : Nat → (Nat × Nat) × List Dec)
    (decf : Flapjack.SemanticPrimitivesHOL.Value → Option (SourceToFlat.Config × β)) :
    st.oracle = f ∘ cakeOrac asmConf c' syn id id →
    (∀ (x : Flapjack.Compiler.Backend.Backend.Config × BackendProgs width) (k : Nat)
        (envId : Nat × Nat) (stV : Flapjack.SemanticPrimitivesHOL.Value) (decs : List Dec),
      x = cakeOrac asmConf c' syn id id k →
      f x = (envId, stV, decs) →
      decs = x.2.sourceProg ∧ envId = x.2.envId ∧
        ∃ dSt, decf stV = some dSt ∧ dSt.1 = x.1.sourceConf) →
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

/-- A successful evaluation-compiler call on an encoded configuration
returns the encoding of the next `compile_inc_progs` configuration
(Flapjack helper shared by the two oracle lemmas below). -/
private theorem mkCompilerFunFromCi_step {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (ci : CompilerInstance Flapjack.Compiler.Backend.Backend.Config)
    (hwf : optEvalConfigWf asmConf c' (some ci))
    (C : Flapjack.Compiler.Backend.Backend.Config) (e : Nat × Nat) (d : List Dec)
    (result : Value × List (BitVec 8) × List (BitVec 64))
    (hres : mkCompilerFunFromCi ci (e, ci.configV C, d) = some result) :
    result.1 = ci.configV (compileIncProgs true asmConf C (e, d)).1 := by
  have hwf' := hwf
  obtain ⟨hfun, -, -⟩ := hwf'
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

/-- Exact HOL `cake_orac_eq_get_oracle` (`backendProofScript.sml:3081-3125`,
`[local]`). HOL `I ## SND` is `Prod.map id Prod.snd`, `I` is `id`, `K concrete_v`
is the constant predicate of the reviewed `oracle_semantics_prog`; HOL's free
`syntax` (a Lean keyword) is `syn` and the case split on `r` is a match. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_eq_get_oracle"
  (words_as_type_indexed_bitvec)]
theorem cakeOrac_eq_getOracle {width : Nat} [NeZero width] {σ : Type}
    (s : Flapjack.SemanticPrimitivesHOL.State σ) (env : SemEnv Flapjack.SemanticPrimitivesHOL.Value) (prog : List Dec) (asmConf : AsmConfigExact width)
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (ci : CompilerInstance Flapjack.Compiler.Backend.Backend.Config)
    (syn : Nat → (Nat × Nat) × List Dec) (s' : Flapjack.SemanticPrimitivesHOL.State σ) :
    ¬ SemanticsHOL.semanticsProg s env prog .fail ∧ optEvalConfigWf asmConf c' (some ci) ∧
      NamespaceHOL.nsAll (fun _ value => concreteValue value = true) env.v ∧ s.refs = [] ∧
      s.evalState = some (mkInitEvalState ci) ∧
      (∀ i r, getOracle ci s env prog i = some r → syn i = Prod.map id Prod.snd r) ∧
      s' = s →
    ∀ (i : Nat) (r : (Nat × Nat) × Flapjack.SemanticPrimitivesHOL.Value × List Dec)
      (x : Flapjack.Compiler.Backend.Backend.Config × (Nat × Nat) × List Dec),
      getOracle ci s' env prog i = some r ∧
        cakeOrac asmConf c' syn id (fun ps => (ps.envId, ps.sourceProg)) i = x →
      match r with
      | (id', cfgV, ds) => ∃ cfg, cfgV = ci.configV cfg ∧ x = (cfg, id', ds) := by
  rintro ⟨noFail, hwf, concrete, refs, initEval, hsyn, rfl⟩
  have props := get_oracle_props env s' ci prog ⟨concrete, refs, initEval, noFail⟩
  have horac : ∀ i, cakeOrac asmConf c' syn id (fun ps => (ps.envId, ps.sourceProg)) i =
      (cakeConfigs asmConf c' syn i, (syn i).1, (syn i).2) := by
    intro i
    rw [cakeOrac_eq_pair, (compileIncProgs_srcEnv asmConf _ (syn i)).1,
      (compileIncProgs_srcEnv asmConf _ (syn i)).2]
    rfl
  intro i
  induction i with
  | zero =>
    rintro ⟨e, v, d⟩ x ⟨hr, rfl⟩
    have hv := props.1 _ hr
    have hs := hsyn 0 _ hr
    refine ⟨c', ?_, ?_⟩
    · rw [← hwf.2.2]; exact hv
    · rw [horac, hs]; rfl
  | succ n ih =>
    rintro ⟨e, v, d⟩ x ⟨hr, rfl⟩
    obtain ⟨r0, x0, hr0, hcomp, hv⟩ := props.2 n _ hr
    obtain ⟨e0, v0, d0⟩ := r0
    obtain ⟨cfg0, hv0, hx0⟩ := ih (e0, v0, d0) _ ⟨hr0, rfl⟩
    rw [horac] at hx0
    simp only [Prod.mk.injEq] at hx0
    obtain ⟨hcfg, he0, hd0⟩ := hx0
    rw [hv0] at hcomp
    have hstep := mkCompilerFunFromCi_step asmConf c' ci hwf cfg0 e0 d0 x0 hcomp
    have hs := hsyn (n + 1) _ hr
    refine ⟨cakeConfigs asmConf c' syn (n + 1), ?_, ?_⟩
    · simp only at hv
      rw [hv, hstep]
      show ci.configV (compileIncProgs true asmConf cfg0 (e0, d0)).1 =
        ci.configV (compileIncProgs true asmConf (cakeConfigs asmConf c' syn n) (syn n)).1
      rw [← hcfg]
      congr 3
      exact Prod.ext he0.symm hd0.symm
    · rw [horac, hs]; rfl

end Flapjack.Compiler.Backend.BackendProof
