module

public import Flapjack.Compiler.Backend.BackendProof.CakeOrac
public import Flapjack.Compiler.Backend.BackendProof.CakeOracConfig

@[expose] public section

/-! backendProofScript.sml 404-442: `cake_orac_config_eqs`, the static
configuration fields that every configuration of the incremental oracle
shares with the initial configuration of a successful compilation. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.Backend
open Flapjack.Compiler.Backend.BackendDefs Flapjack.Compiler.Backend.ClosKnown

/-- Flapjack infrastructure: the tuple of static fields named by HOL's
`cake_orac_config_inv_f` (`backendProofScript.sml:404-408`). -/
private def staticFields (c : Flapjack.Compiler.Backend.Backend.Config) :=
  (c.sourceConf.patternCfg, c.closConf.maxApp, c.closConf.doCall, c.closConf.knownConf.isSome,
    knownStaticConf c.closConf.knownConf, c.closConf.doMti, c.bvlConf.inlineSizeLimit,
    c.bvlConf.splitMainAtSeq, c.bvlConf.expCut, c.bvlConf.doTailrec, c.bvlConf.doTmc,
    c.dataConf, c.wordToWordConf.regAlg, c.stackConf)

/-- Flapjack helper: the static closure fields after the incremental
closure-to-BVL compiler. -/
private theorem closToBvlCompileInc_static (cfg : ClosToBvl.Config)
    (p : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) :
    let r := (ClosToBvl.closToBvlCompileInc cfg p).1
    r.maxApp = cfg.maxApp ∧ r.doCall = cfg.doCall ∧ r.doMti = cfg.doMti ∧
      r.knownConf.isSome = cfg.knownConf.isSome ∧
      knownStaticConf r.knownConf = knownStaticConf cfg.knownConf := by
  have hk : ∃ a, (ClosToBvl.closToBvlCompileInc cfg p).1.knownConf =
      optionUpdValSpt a cfg.knownConf := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := hk
  have e := known_optionUpdValSpt_eq a cfg.knownConf
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · rw [ha]; exact Bool.eq_iff_iff.mpr e.1
  · rw [ha]; exact e.2

/-- Flapjack helper: the static closure fields after the whole-program
closure-to-BVL compiler. -/
private theorem closToBvlCompile_static (cfg : ClosToBvl.Config) (e : List ClosLang.Exp) :
    let r := (ClosToBvl.compileSource cfg e).1
    r.maxApp = cfg.maxApp ∧ r.doCall = cfg.doCall ∧ r.doMti = cfg.doMti ∧
      r.knownConf.isSome = cfg.knownConf.isSome ∧
      knownStaticConf r.knownConf = knownStaticConf cfg.knownConf := by
  have hk : ∃ es, (ClosToBvl.compileSource cfg e).1.knownConf =
      (ClosKnown.compileSource cfg.knownConf es).1 := ⟨_, rfl⟩
  obtain ⟨es, ha⟩ := hk
  rcases hc : ClosKnown.compileSource cfg.knownConf es with ⟨kc, es'⟩
  rw [hc] at ha
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · rw [ha]; exact Bool.eq_iff_iff.mpr (knownCompile_isSome _ _ _ _ hc)
  · rw [ha]; exact knownCompile_staticConf _ _ _ _ hc

/-- Flapjack helper: the whole-program source compiler keeps its pattern settings. -/
private theorem compileTotal_patternCfg (c : SourceToFlat.Config) (p : List AstHOL.Dec) :
    (SourceToFlat.compileTotal c p).1.patternCfg = c.patternCfg :=
  (sourceCompile_patternCfg c p _ _ (0, 0)).1 rfl

private theorem closCompile_maxApp (cfg : ClosToBvl.Config) (e : List ClosLang.Exp) :
    (ClosToBvl.compileSource cfg e).1.maxApp = cfg.maxApp := (closToBvlCompile_static cfg e).1

private theorem closCompile_doCall (cfg : ClosToBvl.Config) (e : List ClosLang.Exp) :
    (ClosToBvl.compileSource cfg e).1.doCall = cfg.doCall := (closToBvlCompile_static cfg e).2.1

private theorem closCompile_doMti (cfg : ClosToBvl.Config) (e : List ClosLang.Exp) :
    (ClosToBvl.compileSource cfg e).1.doMti = cfg.doMti := (closToBvlCompile_static cfg e).2.2.1

private theorem closCompile_isSome (cfg : ClosToBvl.Config) (e : List ClosLang.Exp) :
    (ClosToBvl.compileSource cfg e).1.knownConf.isSome = cfg.knownConf.isSome :=
  (closToBvlCompile_static cfg e).2.2.2.1

private theorem closCompile_staticConf (cfg : ClosToBvl.Config) (e : List ClosLang.Exp) :
    knownStaticConf (ClosToBvl.compileSource cfg e).1.knownConf = knownStaticConf cfg.knownConf :=
  (closToBvlCompile_static cfg e).2.2.2.2

/-- Flapjack helper: one incremental compilation keeps the static fields. -/
private theorem staticFields_step {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (p : (Nat × Nat) × List AstHOL.Dec) :
    staticFields (compileIncProgs true asmConf c p).1 = staticFields c := by
  obtain ⟨envId, decs⟩ := p
  have hs : ∃ q, (compileIncProgs true asmConf c (envId, decs)).1.sourceConf =
      (SourceToFlat.incCompile envId c.sourceConf q).1 := ⟨_, rfl⟩
  have hc : ∃ q, (compileIncProgs true asmConf c (envId, decs)).1.closConf =
      (ClosToBvl.closToBvlCompileInc c.closConf q).1 := ⟨_, rfl⟩
  have hb : ∃ q, (compileIncProgs true asmConf c (envId, decs)).1.bvlConf =
      (BvlToBvi.bvlToBviCompileIncAll c.bvlConf q).1 := ⟨_, rfl⟩
  obtain ⟨qs, hs⟩ := hs
  obtain ⟨qc, hc⟩ := hc
  obtain ⟨qb, hb⟩ := hb
  have hd : (compileIncProgs true asmConf c (envId, decs)).1.dataConf = c.dataConf := rfl
  have hw : (compileIncProgs true asmConf c (envId, decs)).1.wordToWordConf =
      c.wordToWordConf := rfl
  have hst : (compileIncProgs true asmConf c (envId, decs)).1.stackConf = c.stackConf := rfl
  rcases hsrc : SourceToFlat.incCompile envId c.sourceConf qs with ⟨sc, sp⟩
  have hpat := (sourceCompile_patternCfg c.sourceConf qs sc sp envId).2 hsrc
  rw [hsrc] at hs
  obtain ⟨m1, m2, m3, m4, m5⟩ := closToBvlCompileInc_static c.closConf qc
  simp only [staticFields, hs, hc, hb, hd, hw, hst, hpat, m1, m2, m3, m4, m5]
  rfl

/-- Flapjack helper: a successful compilation keeps the static fields. -/
private theorem staticFields_compile {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (h : BackendDefs.compile asmConf c prog = some (b, bm, c')) :
    staticFields c' = staticFields c := by
  simp only [BackendDefs.compile] at h
  obtain ⟨bytes, lc, -, hr⟩ := attachBitmaps_some _ _ _ _ _ h
  simp only [Prod.mk.injEq] at hr
  obtain ⟨-, -, rfl⟩ := hr
  simp only [staticFields, compileTotal_patternCfg, closCompile_maxApp, closCompile_doCall,
    closCompile_doMti, closCompile_isSome, closCompile_staticConf]

/-- Exact HOL `cake_orac_config_eqs` (`backendProofScript.sml:419-442`), whose
statement is the splice `^orac_eq_prop` of `cake_orac_config_inv_f`, captured
expanded: under a successful compilation, every oracle configuration
`cake_configs asm_conf c' src x` keeps fourteen static fields of `c`. HOL's
`⇔` between booleans is `= true ↔ = true`; `IS_SOME` is `Option.isSome`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_config_eqs"
  (words_as_type_indexed_bitvec)]
theorem cakeOrac_configEqs {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (src : Nat → (Nat × Nat) × List AstHOL.Dec) (x : Nat) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') →
      (cakeConfigs asmConf c' src x).sourceConf.patternCfg = c.sourceConf.patternCfg ∧
      (cakeConfigs asmConf c' src x).closConf.maxApp = c.closConf.maxApp ∧
      ((cakeConfigs asmConf c' src x).closConf.doCall = true ↔ c.closConf.doCall = true) ∧
      ((cakeConfigs asmConf c' src x).closConf.knownConf.isSome = true ↔
        c.closConf.knownConf.isSome = true) ∧
      knownStaticConf (cakeConfigs asmConf c' src x).closConf.knownConf =
        knownStaticConf c.closConf.knownConf ∧
      ((cakeConfigs asmConf c' src x).closConf.doMti = true ↔ c.closConf.doMti = true) ∧
      (cakeConfigs asmConf c' src x).bvlConf.inlineSizeLimit = c.bvlConf.inlineSizeLimit ∧
      ((cakeConfigs asmConf c' src x).bvlConf.splitMainAtSeq = true ↔
        c.bvlConf.splitMainAtSeq = true) ∧
      (cakeConfigs asmConf c' src x).bvlConf.expCut = c.bvlConf.expCut ∧
      ((cakeConfigs asmConf c' src x).bvlConf.doTailrec = true ↔ c.bvlConf.doTailrec = true) ∧
      ((cakeConfigs asmConf c' src x).bvlConf.doTmc = true ↔ c.bvlConf.doTmc = true) ∧
      (cakeConfigs asmConf c' src x).dataConf = c.dataConf ∧
      (cakeConfigs asmConf c' src x).wordToWordConf.regAlg = c.wordToWordConf.regAlg ∧
      (cakeConfigs asmConf c' src x).stackConf = c.stackConf := by
  intro h
  have hc' := staticFields_compile asmConf c prog b bm c' h
  have := (cakeConfigs_eq asmConf c prog b bm c' src x staticFields
    ⟨h, hc', staticFields_step asmConf⟩).2
  simp only [staticFields, Prod.mk.injEq] at this
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := this
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  simp

end Flapjack.Compiler.Backend.BackendProof
