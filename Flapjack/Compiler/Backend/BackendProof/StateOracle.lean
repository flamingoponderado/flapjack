module

public import Flapjack.Compiler.Backend.BackendProof.CakeOracConfigEqs
public import Flapjack.Compiler.Backend.BackendProof.ConfigTuple
public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic

@[expose] public section

/-! backendProofScript.sml 1007-1092: the oracles derived from `cake_orac`
are state oracles of the incremental passes, and `state_co` factors through
the per-entry `state_co_fun`. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.Backend
open Flapjack.Compiler.Backend.BackendDefs Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.ClosKnown

/-- Exact HOL `backendProof$state_co_fun_def` (`backendProofScript.sml:1007-1012`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "state_co_fun_def"]
def stateCoFun {α β γ δ ε : Type} (fInc : γ → δ → ε × β) (x : (γ × α) × δ) : α × β :=
  let ((cfg1, cfg2), p) := x
  let (_, p') := fInc cfg1 p
  (cfg2, p')

/-- Exact HOL `state_co_eq_comp` (`backendProofScript.sml:1014-1018`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "state_co_eq_comp"]
theorem stateCo_eq_comp {α β γ δ ε ζ : Type} (fInc : δ → ε → ζ × γ)
    (orac : α → (δ × β) × ε) :
    stateCo fInc orac = stateCoFun fInc ∘ orac := by
  funext n
  rfl

/-- Exact HOL `is_state_oracle_cake_orac_comp` (`backendProofScript.sml:1020-1037`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "is_state_oracle_cake_orac_comp"
  (words_as_type_indexed_bitvec)]
theorem isStateOracle_cakeOracComp {width : Nat} [NeZero width] {α γ δ ε ζ η : Type}
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syn : Nat → (Nat × Nat) × List AstHOL.Dec) (f : η × α → (γ × δ) × ε)
    (g : Flapjack.Compiler.Backend.Backend.Config → η) (h : BackendProgs width → α)
    (fInc : γ → ε → γ × ζ) :
    (∀ (i : Nat) (ps' : α),
      let (c'', ps) := compileIncProgs true asmConf (cakeConfigs asmConf c' syn i) (syn i)
      let ((fc, _), fp) := f (g (cakeConfigs asmConf c' syn i), h ps)
      let ((fc', _), _) := f (g c'', ps')
      fc' = (fInc fc fp).1) →
      isStateOracle fInc (f ∘ cakeOrac asmConf c' syn g h) := by
  intro H n
  have hn := H n (h (compileIncProgs true asmConf (cakeConfigs asmConf c' syn (n + 1))
    (syn (n + 1))).2)
  have e : ∀ i, cakeOrac asmConf c' syn g h i =
      (g (cakeConfigs asmConf c' syn i),
        h (compileIncProgs true asmConf (cakeConfigs asmConf c' syn i) (syn i)).2) := by
    intro i
    rcases hp : compileIncProgs true asmConf (cakeConfigs asmConf c' syn i) (syn i) with ⟨a, b⟩
    simp only [cakeOrac, hp]
  have hs : cakeConfigs asmConf c' syn (n + 1) =
      (compileIncProgs true asmConf (cakeConfigs asmConf c' syn n) (syn n)).1 := rfl
  simp only [Function.comp_apply, e]
  rw [hs] at hn ⊢
  rcases hp : compileIncProgs true asmConf (cakeConfigs asmConf c' syn n) (syn n) with ⟨c1, p1⟩
  simp only [hp] at hn
  simp only at hn ⊢
  rcases hf1 : f (g (cakeConfigs asmConf c' syn n), h p1) with ⟨⟨fc, x⟩, fp⟩
  rcases hf2 : f (g c1, h (compileIncProgs true asmConf c1 (syn (n + 1))).2) with ⟨⟨fc', y⟩, z⟩
  rw [hf1, hf2] at hn
  exact hn

/-- Exact HOL `is_state_oracle_cake_orac` (`backendProofScript.sml:1039-1041`):
`is_state_oracle_cake_orac_comp` at `f = I`; the premise keeps HOL's `I`
applications, the conclusion drops `I o` as HOL's `I_o_ID` rewrite does. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "is_state_oracle_cake_orac"
  (words_as_type_indexed_bitvec)]
theorem isStateOracle_cakeOrac {width : Nat} [NeZero width] {ψ ω ζ ζ' : Type}
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syn : Nat → (Nat × Nat) × List AstHOL.Dec)
    (g : Flapjack.Compiler.Backend.Backend.Config → ψ × ω) (h : BackendProgs width → ζ')
    (fInc : ψ → ζ' → ψ × ζ) :
    (∀ (i : Nat) (ps' : ζ'),
      let (c'', ps) := compileIncProgs true asmConf (cakeConfigs asmConf c' syn i) (syn i)
      let ((fc, _), fp) := id (g (cakeConfigs asmConf c' syn i), h ps)
      let ((fc', _), _) := id (g c'', ps')
      fc' = (fInc fc fp).1) →
      isStateOracle fInc (cakeOrac asmConf c' syn g h) :=
  isStateOracle_cakeOracComp asmConf c' syn id g h fInc

/-- Exact HOL `cake_orac_clos_is_state` (`backendProofScript.sml:1043-1052`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_clos_is_state"
  (words_as_type_indexed_bitvec)]
theorem cakeOrac_closIsState {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syn : Nat → (Nat × Nat) × List AstHOL.Dec) :
    isStateOracle ClosToBvl.closToBvlCompileInc
      (cakeOrac asmConf c' syn (fun c => (c.closConf, ())) (fun ps => ps.closProg)) := by
  apply isStateOracle_cakeOrac
  intro i ps'
  rfl

/-- Exact HOL `cake_orac_source_is_state` (`backendProofScript.sml:1054-1064`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_source_is_state"
  (words_as_type_indexed_bitvec)]
theorem cakeOrac_sourceIsState {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syn : Nat → (Nat × Nat) × List AstHOL.Dec) :
    isStateOracle
      (fun (c : SourceToFlat.Config) ((envId, decs) : (Nat × Nat) × List AstHOL.Dec) =>
        SourceToFlat.incCompile envId c (SourceToSource.compile decs))
      (cakeOrac asmConf c' syn configTuple1 (fun ps => (ps.envId, ps.sourceProg))) := by
  apply isStateOracle_cakeOrac
  intro i ps'
  rfl


/-- Flapjack rendering of HOL's spliced `cake_orac_config_inv_f`
(`backendProofScript.sml:404-408`): the static configuration fields compared
by `is_state_oracle_cake_orac_to_comp`; untagged notation, not a HOL
definition. -/
def cakeOracConfigInvF {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) :=
  ((fun (x : SourceToFlat.Config × ClosToBvl.Config × BvlToBvi.Config ×
      (DataToWord.Config × Nat × StackToLab.Config × AsmConfigExact width)) =>
    let (sc, cc, bc, mc) := x
    (sc.patternCfg, cc.maxApp, cc.doCall, cc.knownConf.isSome, knownStaticConf cc.knownConf,
      cc.doMti, bc.inlineSizeLimit, bc.splitMainAtSeq, bc.expCut, bc.doTailrec, bc.doTmc, mc)) ∘
  (fun (c : Flapjack.Compiler.Backend.Backend.Config) =>
    (c.sourceConf, c.closConf, c.bvlConf, c.dataConf, c.wordToWordConf.regAlg, c.stackConf,
      asmConf))) c

/-- Exact HOL `is_state_oracle_cake_orac_to_comp` (`backendProofScript.sml:1070-1092`).
The spliced `^cake_orac_config_inv_f` is unfolded through the untagged
`cakeOracConfigInvF` notation (the same two composed lambdas as captured);
all type variables of the capture stay independent. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "is_state_oracle_cake_orac_to_comp"
  (words_as_type_indexed_bitvec)]
theorem isStateOracle_cakeOracToComp {width : Nat} [NeZero width]
    {β γ δ ε ζ η θ ι κ K : Type}
    (fInc : β → γ → β × δ) (asmConf : AsmConfigExact width)
    (c' : Flapjack.Compiler.Backend.Backend.Config) (syn : Nat → (Nat × Nat) × List AstHOL.Dec)
    (stF : Flapjack.Compiler.Backend.Backend.Config → β × ε) (psF : BackendProgs width → γ)
    (c : Flapjack.Compiler.Backend.Backend.Config) (prog : List AstHOL.Dec)
    (b : List (BitVec 8)) (bm : List (BitVec width))
    (adj : K × ζ → (η × θ) × ι) (g : Flapjack.Compiler.Backend.Backend.Config → K)
    (h : BackendProgs width → ζ) (gInc : η → ι → η × κ) :
    isStateOracle fInc (cakeOrac asmConf c' syn stF psF) →
    BackendDefs.compile asmConf c prog = some (b, bm, c') →
    (∀ (c'' : Flapjack.Compiler.Backend.Backend.Config) (ps : BackendProgs width)
        (c₃ : Flapjack.Compiler.Backend.Backend.Config) (gP' : ζ),
      cakeOracConfigInvF asmConf c'' = cakeOracConfigInvF asmConf c →
        let (fC', _) := fInc (stF c'').1 (psF ps)
        let ((gC, _), gP) := adj (g c'', h ps)
        let (gC', _) := gInc gC gP
        fC' = (stF c₃).1 → gC' = (adj (g c₃, gP')).1.1) →
    isStateOracle gInc (adj ∘ cakeOrac asmConf c' syn g h) := by
  intro hf hc H n
  have e : ∀ {A B : Type} (g' : Flapjack.Compiler.Backend.Backend.Config → A)
      (h' : BackendProgs width → B) (i : Nat),
      cakeOrac asmConf c' syn g' h' i =
        (g' (cakeConfigs asmConf c' syn i),
          h' (compileIncProgs true asmConf (cakeConfigs asmConf c' syn i) (syn i)).2) := by
    intro A B g' h' i
    rcases hp : compileIncProgs true asmConf (cakeConfigs asmConf c' syn i) (syn i) with ⟨a, b⟩
    simp only [cakeOrac, hp]
  have hfn := hf n
  simp only [e] at hfn
  have hinv : cakeOracConfigInvF asmConf (cakeConfigs asmConf c' syn n) =
      cakeOracConfigInvF asmConf c := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
      cakeOrac_configEqs asmConf c prog b bm c' syn n hc
    simp only [cakeOracConfigInvF, Function.comp_apply, h1, h2, h5, h7, h9, h12, h13, h14,
      Bool.eq_iff_iff.mpr h3, Bool.eq_iff_iff.mpr h4, Bool.eq_iff_iff.mpr h6,
      Bool.eq_iff_iff.mpr h8, Bool.eq_iff_iff.mpr h10, Bool.eq_iff_iff.mpr h11]
  have := H (cakeConfigs asmConf c' syn n)
    (compileIncProgs true asmConf (cakeConfigs asmConf c' syn n) (syn n)).2
    (cakeConfigs asmConf c' syn (n + 1))
    (h (compileIncProgs true asmConf (cakeConfigs asmConf c' syn (n + 1)) (syn (n + 1))).2) hinv
  simp only [Function.comp_apply, e]
  rcases hF : fInc (stF (cakeConfigs asmConf c' syn n)).1
      (psF (compileIncProgs true asmConf (cakeConfigs asmConf c' syn n) (syn n)).2) with ⟨fc, x⟩
  simp only [hF] at this hfn
  rcases hA : adj (g (cakeConfigs asmConf c' syn n),
      h (compileIncProgs true asmConf (cakeConfigs asmConf c' syn n) (syn n)).2) with
    ⟨⟨gc, y⟩, gp⟩
  simp only [hA] at this
  rcases hG : gInc gc gp with ⟨gc', z⟩
  simp only [hG] at this
  exact (this hfn.symm).symm

end Flapjack.Compiler.Backend.BackendProof
