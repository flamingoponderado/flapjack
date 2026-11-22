module

public import Flapjack.Compiler.Backend.BackendProof.LabOracle
public import Flapjack.Compiler.Backend.BackendProof.WordLabelsOk
public import Flapjack.Compiler.Backend.BackendProof.WordConf
public import Flapjack.Compiler.Backend.BviToData.Proofs.Program
public import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileKeys

@[expose] public section

set_option autoImplicit false

/-! backendProofScript.sml 1874-1965: label monotonicity of the `cake_orac`
programs from the stack level down to the lab level. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.BackendDefs Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.LabLang

/-- Exact HOL `monotonic_labels_stack_to_lab` (`backendProofScript.sml:1874-1913`).
HOL `set` of a list is its membership set, `count (SUC n)` is `{m | m < n + 1}`,
`(≠)` is `fun x y => x ≠ y`, `domain` is `sptDomain`; the six-fold `SND`
projection is written with `Prod.snd`; `syntax` is `syntaxOrac`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "monotonic_labels_stack_to_lab"
  (words_as_type_indexed_bitvec)]
theorem monotonicLabels_stackToLab {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syntaxOrac : Nat → (Nat × Nat) × List AstHOL.Dec) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') ∧ backendConfigOk asmConf c →
      oracleMonotonic ((fun l => {x | x ∈ l}) ∘
          List.map (Prod.fst : Nat × StackLang.HolProg width → Nat) ∘
          (Prod.fst : List (Nat × StackLang.HolProg width) × List (BitVec width) → _) ∘
          Prod.snd)
        (fun x y => x ≠ y)
        ({x | x ∈ (toStack asmConf c prog).2.2.1.map Prod.fst} ∪
          {m | m < StackLang.gcStubLocation + 1})
        (cakeOrac asmConf c' syntaxOrac
          (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
          (fun ps => (ps.stackProg, ps.curBm))) →
      oracleMonotonic ((fun l => {x | x ∈ l}) ∘
          List.map (fun sec : LabLang.Section (Line (AsmOrCbw (HolAsm width) HolMemop
            (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width)
              Flapjack.Basis.Pure.MlString.MlString) (BitVec width)) => sec.sectionId) ∘
          Prod.snd)
        (fun x y => x ≠ y) {x | sptDomain c'.labConf.labels x}
        (cakeOrac asmConf c' syntaxOrac
          (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
          (fun ps => ps.labProg)) := by
  intro h hm
  refine oracleMonotonic_subset _ _ _ _ _ _ _ ⟨?_, ?_⟩ hm
  · intro x hx
    have hok := toLab_labelsOk asmConf c prog b bm c' h
    have hcfg := h.2
    have hc := h.1
    rw [compile_eq_toTarget] at hc
    unfold toTarget at hc
    rcases hl : toLab asmConf c prog with ⟨bm1, c1, p1, names1⟩
    rw [hl] at hc hok
    obtain ⟨bytes, c2, hlab, hr⟩ := attachBitmaps_some _ _ _ _ _ hc
    have hc' : c' = _ := (congrArg (fun r => r.2.2) hr)
    subst hc'
    change sptDomain c2.labels x at hx
    have hd := compileLab_domainLabels asmConf _ _ bytes c2 hlab
    rw [hd, LabToTarget.FilterSkip.getCodeLabelsFilterSkip,
      stackLabelsOk_fstCodeLabels_sectionNum _ hok] at hx
    rcases hw : toWord asmConf c prog with ⟨cw, pw, nw⟩
    have hwl := toWord_labConf asmConf c cw prog pw nw hw
    rcases hn : WordToStack.Native.compileNative asmConf cw.stackConf.perfCalls pw with
      ⟨bmn, wcn, fsn, pn⟩
    simp only [toLab, toStack, hw, hn, Prod.mk.injEq] at hl
    obtain ⟨-, rfl, rfl, -⟩ := hl
    simp only [toStack, hw, hn]
    rcases hx with hx | hx
    · exact mapSectionNum_stackToLab_subset _ _ _ _ _ _ _
        ⟨Set.subset_union_left, Set.subset_union_right⟩ hx
    · have hc1 : cw.labConf.labels = .ln := by
        rw [← hwl]
        exact hcfg.2.2.2.2.2.1
      change sptDomain cw.labConf.labels x at hx
      rw [hc1] at hx
      exact absurd hx (by simp [sptDomain])
  · intro n
    rw [cakeOrac_eq_pair, cakeOrac_eq_pair]
    intro x hx
    simp only [Function.comp, Set.mem_ofPred_eq] at hx ⊢
    unfold compileIncProgs at hx ⊢
    simp only [keepProgs_true, id] at hx ⊢
    unfold StackToLab.compileNoStubs at hx
    rw [StackToLab.Proofs.CodeInstalled.mapProgToSectionSectionNum,
      StackNames.map_fst_compileHOL, List.map_map, List.map_map] at hx
    convert hx using 2
    funext q
    rfl

/-- Exact HOL `monotonic_labels_bvi_down_to_stack` (`backendProofScript.sml:1915-1965`).
HOL `set` of a list is its membership set, `count (SUC n)` is `{m | m < n + 1}`,
`(≠)` is `fun x y => x ≠ y`; the `SND` projections are written with
`Prod.snd`; `syntax` is `syntaxOrac`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "monotonic_labels_bvi_down_to_stack"
  (words_as_type_indexed_bitvec)]
theorem monotonicLabels_bviDownToStack {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syntaxOrac : Nat → (Nat × Nat) × List AstHOL.Dec) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') ∧ backendConfigOk asmConf c →
      oracleMonotonic ((fun l => {x | x ∈ l}) ∘
          List.map (Prod.fst : Nat × Nat × Bvi.Exp → Nat) ∘ Prod.snd)
        (fun x y => x ≠ y)
        ({x | x ∈ (Flapjack.Compiler.Backend.Backend.toBvi c prog).2.1.map Prod.fst} ∪
          {m | m < dataNumStubs + 1})
        (cakeOrac asmConf c' syntaxOrac
          (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
          (fun ps => ps.bviProg)) →
      oracleMonotonic ((fun l => {x | x ∈ l}) ∘
          List.map (Prod.fst : Nat × StackLang.HolProg width → Nat) ∘
          (Prod.fst : List (Nat × StackLang.HolProg width) × List (BitVec width) → _) ∘
          Prod.snd)
        (fun x y => x ≠ y)
        ({x | x ∈ (toStack asmConf c prog).2.2.1.map Prod.fst} ∪
          {m | m < StackLang.gcStubLocation + 1})
        (cakeOrac asmConf c' syntaxOrac
          (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
          (fun ps => (ps.stackProg, ps.curBm))) := by
  intro h hm
  refine oracleMonotonic_subset _ _ _ _ _ _ _ ⟨?_, ?_⟩ hm
  · have hperf : c.stackConf.perfCalls = false := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hword := toWord_labelsOk asmConf c prog b bm c' h
    rcases hw : toWord asmConf c prog with ⟨cw, pw, names⟩
    rw [hw] at hword
    obtain ⟨-, -, hlabs⟩ := hword
    have hperf' : cw.stackConf.perfCalls = false := by
      rw [← toWord_perfCalls asmConf c cw prog pw names hw, hperf]
    have hstack := WordToStack.Native.ExtractLabelsCompiler.wordToStackCompileLabPres asmConf pw
      hlabs
    rcases hb : Flapjack.Compiler.Backend.Backend.toBvi c prog with ⟨cb, pb, nb⟩
    have hpw : pw.map Prod.fst =
        (DataToWord.stubs cb.dataConf : List (Nat × Nat × WordLangProgHOL (BitVec width))).map
          Prod.fst ++ pb.map Prod.fst := by
      have hlab := DataToWord.Proofs.dataToWord_compileLabPres (width := width) cb.dataConf
        cb.wordToWordConf asmConf (BviToData.compileProg pb)
      simp only [toWord, Flapjack.Compiler.Backend.Backend.toData, hb] at hw
      rcases hc : DataToWord.compile cb.dataConf cb.wordToWordConf asmConf
        (BviToData.compileProg pb) with ⟨col, p⟩
      rw [hc] at hlab hw
      simp only [Prod.mk.injEq] at hw
      rw [← hw.2.1, hlab.1, BviToData.map_fst_compileProg]
    simp only [toStack, hw, hperf']
    intro x hx
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hx ⊢
    have hrs : raiseStubLocation = 5 := rfl
    have hsc : storeConstsStubLocation = 6 := rfl
    have hgc : StackLang.gcStubLocation = 4 := rfl
    have hds : dataNumStubs = 62 := rfl
    rcases hx with hx | hx
    · rw [hstack.1] at hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · right; simp only [hrs, hds]; omega
      · right; simp only [hsc, hds]; omega
      · rw [hpw, List.mem_append] at hx
        rcases hx with hx | hx
        · right; have := DataToWord.Proofs.mapFst_stubs_bound _ _ hx; omega
        · left; exact hx
    · right; simp only [hgc, hds] at hx ⊢; omega
  · intro n
    rw [cakeOrac_eq_pair, cakeOrac_eq_pair]
    intro x hx
    simp only [Function.comp, Set.mem_ofPred_eq] at hx ⊢
    unfold compileIncProgs at hx ⊢
    simp only [keepProgs_true, id] at hx ⊢
    generalize BvlToBvi.bvlToBviCompileIncAll _ _ = q at hx ⊢
    rw [Flapjack.WordToStackProofs.mapFstCompileWordToStack _ _ _ _ _ _ _ rfl] at hx
    simp only [List.map_map] at hx
    convert hx using 2
    rw [← BviToData.map_fst_compileProg q.2]
    refine List.map_congr_left fun e _ => ?_
    rfl

end Flapjack.Compiler.Backend.BackendProof
