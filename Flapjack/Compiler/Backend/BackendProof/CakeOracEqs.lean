module

public import Flapjack.Compiler.Backend.BackendProof.StateOracle
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.FullOracle

@[expose] public section

/-! backendProofScript.sml 496-589: `cake_orac_eqs`, each pass's oracle
derived from the one above it equals the corresponding projection of
`cake_orac`. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.Backend
open Flapjack.Compiler.Backend.BackendDefs Flapjack.Compiler.Backend.BackendProps

/-- Flapjack helper: the entries of `cake_orac`. -/
private theorem cakeOrac_apply {width : Nat} [NeZero width] {A B : Type}
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (src : Nat → (Nat × Nat) × List AstHOL.Dec)
    (g : Flapjack.Compiler.Backend.Backend.Config → A) (h : BackendProgs width → B) (i : Nat) :
    cakeOrac asmConf c' src g h i =
      (g (cakeConfigs asmConf c' src i),
        h (compileIncProgs true asmConf (cakeConfigs asmConf c' src i) (src i)).2) := by
  rcases hp : compileIncProgs true asmConf (cakeConfigs asmConf c' src i) (src i) with ⟨a, b⟩
  simp only [cakeOrac, hp]

/-- Flapjack piece of `cake_orac_eqs`: source to flat. -/
private theorem cakeOracEqs_sourceToFlat {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (src : Nat → (Nat × Nat) × List AstHOL.Dec) :
    stateCo (fun (c : SourceToFlat.Config) ((envId, decs) : (Nat × Nat) × List AstHOL.Dec) =>
        SourceToFlat.incCompile envId c (SourceToSource.compile decs))
      (cakeOrac asmConf c' src configTuple1 (fun ps => (ps.envId, ps.sourceProg))) =
      cakeOrac asmConf c' src (Prod.snd ∘ configTuple1) (fun ps => ps.flatProg) := by
  funext n
  simp only [stateCo, cakeOrac_apply, compileIncProgs_srcEnv]
  rfl


/-- Flapjack piece of `cake_orac_eqs`: flat to closure. -/
private theorem cakeOracEqs_flatToClos {width : Nat} [NeZero width] {β : Type}
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (src : Nat → (Nat × Nat) × List AstHOL.Dec) (f1 : Flapjack.Compiler.Backend.Backend.Config → β) :
    pureCo (FlatToClos.incCompileDecs (α := Nat × Nat × ClosLang.Exp)) ∘
        cakeOrac asmConf c' src f1 (fun ps => ps.flatProg) =
      cakeOrac asmConf c' src f1 (fun ps => ps.closProg) := by
  funext n
  simp only [Function.comp_apply, pureCo, cakeOrac_apply]
  rfl

/-- Flapjack piece of `cake_orac_eqs`: BVI to data. -/
private theorem cakeOracEqs_bviToData {width : Nat} [NeZero width] {γ : Type}
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (src : Nat → (Nat × Nat) × List AstHOL.Dec) (f3 : Flapjack.Compiler.Backend.Backend.Config → γ) :
    pureCo BviToData.compileProg ∘ cakeOrac asmConf c' src f3 (fun ps => ps.bviProg) =
      cakeOrac asmConf c' src f3 (fun ps => ps.dataProg) := by
  funext n
  simp only [Function.comp_apply, pureCo, cakeOrac_apply]
  rfl

set_option maxHeartbeats 1000000 in
/-- Flapjack piece of `cake_orac_eqs`: stack to lab. -/
private theorem cakeOracEqs_stackToLab {width : Nat} [NeZero width] {ε : Type}
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (src : Nat → (Nat × Nat) × List AstHOL.Dec)
    (regNm : Spt Nat) (jump : Bool) (sp : Nat) (offs : BitVec width × BitVec width)
    (f5 : Flapjack.Compiler.Backend.Backend.Config → ε) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') ∧ regNm = c.stackConf.regNames ∧
        jump = c.stackConf.jump ∧ sp = asmConf.regCount - (asmConf.avoidRegs.length + 3) ∧
        offs = asmConf.addrOffset →
      pureCo (StackToLab.compileNoStubs regNm jump offs sp ∘ Prod.fst) ∘
          cakeOrac asmConf c' src f5 (fun ps => (ps.stackProg, ps.curBm)) =
        cakeOrac asmConf c' src f5 (fun ps => ps.labProg) := by
  intro ⟨h, hrn, hj, hsp, hoffs⟩
  subst hrn hj hsp hoffs
  funext n
  have hst := (cakeOrac_configEqs asmConf c prog b bm c' src n h).2.2.2.2.2.2.2.2.2.2.2.2.2
  simp only [Function.comp_apply, pureCo, cakeOrac_apply]
  rw [← hst, show asmConf.avoidRegs.length + 3 = 3 + asmConf.avoidRegs.length by omega]
  rfl

set_option maxHeartbeats 1000000 in
/-- Flapjack piece of `cake_orac_eqs`: data to word. -/
private theorem cakeOracEqs_dataToWord {width : Nat} [NeZero width] {δ : Type}
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (src : Nat → (Nat × Nat) × List AstHOL.Dec)
    (dc : DataToWord.Config) (trC : Bool) (regC regAlg : Nat)
    (f4 : Flapjack.Compiler.Backend.Backend.Config → δ) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') ∧
        dc = ensureFpConfOk asmConf c.dataConf ∧ (trC = true ↔ asmConf.twoRegArith = true) ∧
        regC = asmConf.regCount - (asmConf.avoidRegs.length + 5) ∧
        regAlg = c.wordToWordConf.regAlg →
      pureCo (List.map fun p => WordToWord.fullCompileSingle trC regC regAlg asmConf (p, none)) ∘
          pureCo (List.map (DataToWord.compilePart dc)) ∘
          cakeOrac asmConf c' src f4 (fun ps => ps.dataProg) =
        cakeOrac asmConf c' src f4 (fun ps => ps.wordProg) := by
  intro ⟨h, hdc, htr, hrc, hra⟩
  have htr' : trC = asmConf.twoRegArith := Bool.eq_iff_iff.mpr htr
  subst htr' hdc hrc hra
  funext n
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hd, hr, -⟩ :=
    cakeOrac_configEqs asmConf c prog b bm c' src n h
  simp only [Function.comp_apply, pureCo, cakeOrac_apply]
  rw [← hd, ← hr, show asmConf.avoidRegs.length + 5 = 5 + asmConf.avoidRegs.length by omega]
  rfl


set_option maxHeartbeats 1000000 in
/-- Flapjack piece of `cake_orac_eqs`: word to stack. -/
private theorem cakeOracEqs_wordToStack {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (src : Nat → (Nat × Nat) × List AstHOL.Dec) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') ∧
        (c.stackConf.perfCalls = true ↔ false = true) →
      (fun (x : (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec width))) =>
          let ((bm0, cfg), prg) := x
          (fun (y : List (Nat × StackLang.HolProg width) × List Nat ×
              (AppList (BitVec width) × Nat)) =>
            let (prg2, _fs, bm) := y
            (cfg, prg2, appListAppend bm.1))
            (WordToStack.Native.compileWordToStackNative asmConf false
              (asmConf.regCount - (asmConf.avoidRegs.length + 5)) prg (.nil, bm0))) ∘
          cakeOrac asmConf c' src
            (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
            (fun ps => ps.wordProg) =
        cakeOrac asmConf c' src
          (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
          (fun ps => (ps.stackProg, ps.curBm)) := by
  intro ⟨h, hperf⟩
  have hp : c.stackConf.perfCalls = false := by simpa using hperf
  funext n
  have hst := (cakeOrac_configEqs asmConf c prog b bm c' src n h).2.2.2.2.2.2.2.2.2.2.2.2.2
  simp only [Function.comp_apply, cakeOrac_apply]
  rw [← hp, ← hst, show asmConf.avoidRegs.length + 5 = 5 + asmConf.avoidRegs.length by omega]
  rfl

set_option maxHeartbeats 1000000 in
/-- Flapjack piece of `cake_orac_eqs`: BVL to BVI. -/
private theorem cakeOracEqs_bvlToBvi {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (src : Nat → (Nat × Nat) × List AstHOL.Dec)
    (bvlC : BvlToBvi.Config) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') ∧ bvlC = c.bvlConf →
      BvlToBvi.Proofs.fullCo bvlC (cakeOrac asmConf c' src configTuple2 (fun ps => ps.bvlProg)) =
        cakeOrac asmConf c' src
          (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
          (fun ps => ps.bviProg) := by
  intro ⟨h, hb⟩
  subst hb
  funext n
  obtain ⟨-, -, -, -, -, -, h7, h8, h9, h10, h11, -, -, -⟩ :=
    cakeOrac_configEqs asmConf c prog b bm c' src n h
  have h8' := Bool.eq_iff_iff.mpr h8
  have h10' := Bool.eq_iff_iff.mpr h10
  have h11' := Bool.eq_iff_iff.mpr h11
  simp only [BvlToBvi.Proofs.fullCo, stateCo, cakeOrac_apply]
  rw [← h7, ← h8', ← h9, ← h10', ← h11']
  rfl

set_option maxHeartbeats 1000000 in
/-- Flapjack piece of `cake_orac_eqs`: closure to BVL. -/
private theorem cakeOracEqs_closToBvl {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (src : Nat → (Nat × Nat) × List AstHOL.Dec)
    (closC : ClosToBvl.Config) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') ∧ closC = c.closConf →
      pureCo (ClosToBvl.compileInc closC.maxApp) ∘
          pureCo (ClosAnnotate.compileIncSource (α := Nat)) ∘
          stateCo (ClosCall.condCallCompileInc closC.doCall)
            (ClosKnown.knownCo closC.knownConf
              (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
                (pureCo (ClosMti.condCompileInc closC.doMti closC.maxApp) ∘
                  cakeOrac asmConf c' src (Prod.snd ∘ configTuple1)
                    (fun ps => ps.closProg)))) =
        cakeOrac asmConf c' src configTuple2 (fun ps => ps.bvlProg) := by
  intro ⟨h, hc⟩
  subst hc
  funext n
  obtain ⟨-, h2, h3, -, h5, h6, -, -, -, -, -, -, -, -⟩ :=
    cakeOrac_configEqs asmConf c prog b bm c' src n h
  have h3' := Bool.eq_iff_iff.mpr h3
  have h6' := Bool.eq_iff_iff.mpr h6
  rw [knownCo_eq_stateCo_inc]
  simp only [Function.comp_apply, pureCo, stateCo, cakeOrac_apply]
  rw [← h2, ← h3', ← h5, ← h6']
  rfl


/-- Exact HOL `cake_orac_eqs` (`backendProofScript.sml:496-589`): the eight
oracle equations, one per pass, with free `asm_conf c' src f1 f3 f4 f5 c prog
b bm clos_c bvl_c dc tr_c reg_c reg_alg reg_nm jump sp offs` as in the
capture. HOL `⇔` between booleans is `= true ↔ = true`, `F` is `false`,
`pure_co`/`state_co` are the reviewed `pureCo`/`stateCo`, `##`-free
compositions are `∘`, `MAP` is `List.map`, `append` is `appListAppend`,
`known_co` is `ClosKnown.knownCo` and `full_co` is `BvlToBvi.Proofs.fullCo`.
The capture's independent result types of `f1 f3 f4 f5` stay independent. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_eqs"
  (words_as_type_indexed_bitvec)]
theorem cakeOrac_eqs {width : Nat} [NeZero width] {β γ δ ε : Type}
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (src : Nat → (Nat × Nat) × List AstHOL.Dec) (f1 : Flapjack.Compiler.Backend.Backend.Config → β)
    (c : Flapjack.Compiler.Backend.Backend.Config) (prog : List AstHOL.Dec)
    (b : List (BitVec 8)) (bm : List (BitVec width)) (closC : ClosToBvl.Config)
    (bvlC : BvlToBvi.Config) (f3 : Flapjack.Compiler.Backend.Backend.Config → γ)
    (dc : DataToWord.Config) (trC : Bool) (regC regAlg : Nat)
    (f4 : Flapjack.Compiler.Backend.Backend.Config → δ) (regNm : Spt Nat) (jump : Bool)
    (sp : Nat) (offs : BitVec width × BitVec width)
    (f5 : Flapjack.Compiler.Backend.Backend.Config → ε) :
    stateCo (fun (c : SourceToFlat.Config) ((envId, decs) : (Nat × Nat) × List AstHOL.Dec) =>
        SourceToFlat.incCompile envId c (SourceToSource.compile decs))
      (cakeOrac asmConf c' src configTuple1 (fun ps => (ps.envId, ps.sourceProg))) =
      cakeOrac asmConf c' src (Prod.snd ∘ configTuple1) (fun ps => ps.flatProg) ∧
    pureCo (FlatToClos.incCompileDecs (α := Nat × Nat × ClosLang.Exp)) ∘
        cakeOrac asmConf c' src f1 (fun ps => ps.flatProg) =
      cakeOrac asmConf c' src f1 (fun ps => ps.closProg) ∧
    (BackendDefs.compile asmConf c prog = some (b, bm, c') ∧ closC = c.closConf →
      pureCo (ClosToBvl.compileInc closC.maxApp) ∘
          pureCo (ClosAnnotate.compileIncSource (α := Nat)) ∘
          stateCo (ClosCall.condCallCompileInc closC.doCall)
            (ClosKnown.knownCo closC.knownConf
              (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
                (pureCo (ClosMti.condCompileInc closC.doMti closC.maxApp) ∘
                  cakeOrac asmConf c' src (Prod.snd ∘ configTuple1)
                    (fun ps => ps.closProg)))) =
        cakeOrac asmConf c' src configTuple2 (fun ps => ps.bvlProg)) ∧
    (BackendDefs.compile asmConf c prog = some (b, bm, c') ∧ bvlC = c.bvlConf →
      BvlToBvi.Proofs.fullCo bvlC (cakeOrac asmConf c' src configTuple2 (fun ps => ps.bvlProg)) =
        cakeOrac asmConf c' src
          (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
          (fun ps => ps.bviProg)) ∧
    pureCo BviToData.compileProg ∘ cakeOrac asmConf c' src f3 (fun ps => ps.bviProg) =
      cakeOrac asmConf c' src f3 (fun ps => ps.dataProg) ∧
    (BackendDefs.compile asmConf c prog = some (b, bm, c') ∧
        dc = ensureFpConfOk asmConf c.dataConf ∧ (trC = true ↔ asmConf.twoRegArith = true) ∧
        regC = asmConf.regCount - (asmConf.avoidRegs.length + 5) ∧
        regAlg = c.wordToWordConf.regAlg →
      pureCo (List.map fun p => WordToWord.fullCompileSingle trC regC regAlg asmConf (p, none)) ∘
          pureCo (List.map (DataToWord.compilePart dc)) ∘
          cakeOrac asmConf c' src f4 (fun ps => ps.dataProg) =
        cakeOrac asmConf c' src f4 (fun ps => ps.wordProg)) ∧
    (BackendDefs.compile asmConf c prog = some (b, bm, c') ∧
        (c.stackConf.perfCalls = true ↔ false = true) →
      (fun (x : (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec width))) =>
          let ((bm0, cfg), prg) := x
          (fun (y : List (Nat × StackLang.HolProg width) × List Nat ×
              (AppList (BitVec width) × Nat)) =>
            let (prg2, _fs, bm) := y
            (cfg, prg2, appListAppend bm.1))
            (WordToStack.Native.compileWordToStackNative asmConf false
              (asmConf.regCount - (asmConf.avoidRegs.length + 5)) prg (.nil, bm0))) ∘
          cakeOrac asmConf c' src
            (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
            (fun ps => ps.wordProg) =
        cakeOrac asmConf c' src
          (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
          (fun ps => (ps.stackProg, ps.curBm))) ∧
    (BackendDefs.compile asmConf c prog = some (b, bm, c') ∧ regNm = c.stackConf.regNames ∧
        (jump = true ↔ c.stackConf.jump = true) ∧
        sp = asmConf.regCount - (asmConf.avoidRegs.length + 3) ∧ offs = asmConf.addrOffset →
      pureCo (StackToLab.compileNoStubs regNm jump offs sp ∘ Prod.fst) ∘
          cakeOrac asmConf c' src f5 (fun ps => (ps.stackProg, ps.curBm)) =
        cakeOrac asmConf c' src f5 (fun ps => ps.labProg)) :=
  ⟨cakeOracEqs_sourceToFlat asmConf c' src, cakeOracEqs_flatToClos asmConf c' src f1,
    cakeOracEqs_closToBvl asmConf c prog b bm c' src closC,
    cakeOracEqs_bvlToBvi asmConf c prog b bm c' src bvlC,
    cakeOracEqs_bviToData asmConf c' src f3,
    cakeOracEqs_dataToWord asmConf c prog b bm c' src dc trC regC regAlg f4,
    cakeOracEqs_wordToStack asmConf c prog b bm c' src,
    fun ⟨h, h1, h2, h3, h4⟩ => cakeOracEqs_stackToLab asmConf c prog b bm c' src regNm jump sp
      offs f5 ⟨h, h1, Bool.eq_iff_iff.mpr h2, h3, h4⟩⟩


/-- Exact HOL `stack_to_lab_orac_eq_std_sym` (`backendProofScript.sml:1003-1005`):
the stack-to-lab conjunct of `cake_orac_eqs`, simplified (its equational
premises substituted) and reversed, as HOL's `SIMP_RULE` / `GSYM` derivation
produces. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "stack_to_lab_orac_eq_std_sym"
  (words_as_type_indexed_bitvec)]
theorem stackToLab_oracEq_stdSym {width : Nat} [NeZero width] {ε : Type}
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (src : Nat → (Nat × Nat) × List AstHOL.Dec)
    (f5 : Flapjack.Compiler.Backend.Backend.Config → ε) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') →
      cakeOrac asmConf c' src f5 (fun ps => ps.labProg) =
        pureCo (StackToLab.compileNoStubs c.stackConf.regNames c.stackConf.jump
            asmConf.addrOffset (asmConf.regCount - (asmConf.avoidRegs.length + 3)) ∘ Prod.fst) ∘
          cakeOrac asmConf c' src f5 (fun ps => (ps.stackProg, ps.curBm)) := fun h =>
  (cakeOracEqs_stackToLab asmConf c prog b bm c' src _ _ _ _ f5
    ⟨h, rfl, rfl, rfl, rfl⟩).symm

/-- Exact HOL `data_to_word_orac_eq_std` (`backendProofScript.sml:2670-2671`):
the data-to-word conjunct of `cake_orac_eqs` at
`f4 = SND o SND o SND o SND o SND o config_tuple2`, with all variables
generalised as captured. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "data_to_word_orac_eq_std"
  (words_as_type_indexed_bitvec)]
theorem dataToWord_oracEq_std {width : Nat} [NeZero width] :
    ∀ (trC : Bool) (src : Nat → (Nat × Nat) × List AstHOL.Dec) (regC regAlg : Nat)
      (prog : List AstHOL.Dec) (dc : DataToWord.Config)
      (c' c : Flapjack.Compiler.Backend.Backend.Config) (bm : List (BitVec width))
      (b : List (BitVec 8)) (asmConf : AsmConfigExact width),
      BackendDefs.compile asmConf c prog = some (b, bm, c') ∧
          dc = ensureFpConfOk asmConf c.dataConf ∧ (trC = true ↔ asmConf.twoRegArith = true) ∧
          regC = asmConf.regCount - (asmConf.avoidRegs.length + 5) ∧
          regAlg = c.wordToWordConf.regAlg →
        pureCo (List.map fun p => WordToWord.fullCompileSingle trC regC regAlg asmConf (p, none)) ∘
            pureCo (List.map (DataToWord.compilePart dc)) ∘
            cakeOrac asmConf c' src
              (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
              (fun ps => ps.dataProg) =
          cakeOrac asmConf c' src
            (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
            (fun ps => ps.wordProg) :=
  fun trC src regC regAlg prog dc c' c bm b asmConf =>
    cakeOracEqs_dataToWord asmConf c prog b bm c' src dc trC regC regAlg _

/-- Exact HOL `data_to_word_orac_eq_sym_std` (`backendProofScript.sml:2673-2675`):
`data_to_word_orac_eq_std` with its equational premises substituted and the
equation reversed. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "data_to_word_orac_eq_sym_std"
  (words_as_type_indexed_bitvec)]
theorem dataToWord_oracEq_symStd {width : Nat} [NeZero width] :
    ∀ (src : Nat → (Nat × Nat) × List AstHOL.Dec) (prog : List AstHOL.Dec)
      (c' c : Flapjack.Compiler.Backend.Backend.Config) (bm : List (BitVec width))
      (b : List (BitVec 8)) (asmConf : AsmConfigExact width),
      BackendDefs.compile asmConf c prog = some (b, bm, c') →
        cakeOrac asmConf c' src
            (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
            (fun ps => ps.wordProg) =
          pureCo (List.map fun p => WordToWord.fullCompileSingle asmConf.twoRegArith
              (asmConf.regCount - (asmConf.avoidRegs.length + 5)) c.wordToWordConf.regAlg asmConf
              (p, none)) ∘
            pureCo (List.map (DataToWord.compilePart (ensureFpConfOk asmConf c.dataConf))) ∘
            cakeOrac asmConf c' src
              (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
              (fun ps => ps.dataProg) :=
  fun src prog c' c bm b asmConf h =>
    (cakeOracEqs_dataToWord asmConf c prog b bm c' src _ _ _ _ _
      ⟨h, rfl, Iff.rfl, rfl, rfl⟩).symm

end Flapjack.Compiler.Backend.BackendProof
