module

public import Flapjack.Compiler.Backend.BackendProof.NameDistinct
public import Flapjack.Compiler.Backend.Proofs.WordConventions
public import Flapjack.Compiler.Backend.DataToWord.Proofs.LabPres
public import Flapjack.Compiler.Backend.WordToStack.Proofs.ExtractLabelsCompiler
public import Flapjack.Compiler.Backend.StackToLab.Proofs.CompileLabPres
public import Flapjack.Compiler.Backend.BackendProof.LabLabels
public import Flapjack.Compiler.Backend.BackendProof.CompileLab
public import Flapjack.Compiler.Backend.LabToTarget.FilterSkip

@[expose] public section

set_option autoImplicit false

/-! backendProofScript.sml 1337-1419: the lab programs of `cake_orac` are
well labelled (`stack_to_labProof$labels_ok`). -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.WordConvs Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.BackendDefs Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.LabLang

/-- Transfer of per-procedure label conditions along `labels_rel` (Flapjack
infrastructure for `lab_labels_ok_oracle`). -/
theorem labelsRel_transfer {α : Type} (lab : α → List (Nat × Nat)) :
    ∀ (A B : List (Nat × Nat × α)), B.map Prod.fst = A.map Prod.fst →
      List.Forall₂ labelsRel (A.map fun x => lab x.2.2) (B.map fun x => lab x.2.2) →
      (∀ a ∈ A, (∀ x ∈ lab a.2.2, x.1 = a.1 ∧ x.2 ≠ 0 ∧ x.2 ≠ 1) ∧ (lab a.2.2).Nodup) →
      ∀ b ∈ B, (∀ x ∈ lab b.2.2, x.1 = b.1 ∧ x.2 ≠ 0 ∧ x.2 ≠ 1) ∧ (lab b.2.2).Nodup
  | [], [], _, _, _ => by simp
  | [], _ :: _, hf, _, _ => by simp at hf
  | _ :: _, [], hf, _, _ => by simp at hf
  | a :: A, b :: B, hf, hr, hA => by
      simp only [List.map_cons, List.cons.injEq] at hf
      simp only [List.map_cons, List.forall₂_cons] at hr
      intro r hrm
      rcases List.mem_cons.1 hrm with rfl | hrm
      · obtain ⟨h1, h2⟩ := hA a (List.mem_cons_self ..)
        refine ⟨fun x hx => ?_, hr.1.1 h2⟩
        have := h1 x (hr.1.2 x hx)
        rw [hf.1]; exact this
      · exact labelsRel_transfer lab A B hf.2 hr.2
          (fun a' ha' => hA a' (List.mem_cons_of_mem _ ha')) r hrm

/-- Label conditions of word programs produced from data programs by
`compile_part` followed by the word-to-word optimiser (Flapjack infrastructure
for `lab_labels_ok_oracle`). -/
theorem wordProg_labels {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (dc : DataToWord.Config) (alg : Nat) (dp : List (Nat × Nat × DataLang.Prog)) :
    ∀ row ∈ (dp.map (DataToWord.compilePart (width := width) dc)).map (fun p =>
        WordToWord.fullCompileSingle asmConf.twoRegArith
          (asmConf.regCount - (5 + asmConf.avoidRegs.length)) alg asmConf (p, none)),
      (∀ label ∈ Flapjack.extractLabels row.2.2,
        label.1 = row.1 ∧ label.2 ≠ 0 ∧ label.2 ≠ 1) ∧
      (Flapjack.extractLabels row.2.2).Nodup := by
  have hk : asmConf.regCount - (5 + asmConf.avoidRegs.length) =
      asmConf.regCount - (asmConf.avoidRegs.length + 5) := by omega
  obtain ⟨wc, ign, hwc⟩ := mapFullCompileSingle_to_compile _
    (dp.map (DataToWord.compilePart (width := width) dc)) asmConf
    (asmConf.regCount - (5 + asmConf.avoidRegs.length)) alg ⟨rfl, hk⟩
  have hsrc : ∀ a ∈ dp.map (DataToWord.compilePart (width := width) dc),
      (∀ x ∈ Flapjack.extractLabels a.2.2, x.1 = a.1 ∧ x.2 ≠ 0 ∧ x.2 ≠ 1) ∧
        (Flapjack.extractLabels a.2.2).Nodup := by
    intro a ha
    obtain ⟨⟨nm, ar, body⟩, -, rfl⟩ := List.mem_map.1 ha
    have := DataToWord.Proofs.dataToWord_labPresLem (width := width) dc nm 2 body (by decide)
    rcases hc : DataToWord.compileControl (width := width) dc nm 2 body with ⟨cp, l'⟩
    rw [hc] at this
    obtain ⟨-, h1, h2⟩ := this
    show (∀ x ∈ Flapjack.extractLabels (DataToWord.compileControl dc nm 2 body).1,
        x.1 = nm ∧ x.2 ≠ 0 ∧ x.2 ≠ 1) ∧
      (Flapjack.extractLabels (DataToWord.compileControl dc nm 2 body).1).Nodup
    rw [hc]
    exact ⟨fun x hx => by have := h1 x hx; omega, h2⟩
  have hguard : ∀ x ∈ dp.map (DataToWord.compilePart (width := width) dc),
      noShareInstSubprogsHOL x.2.2 = true ∨ asmConf.isa ≠ .ag32 := by
    intro a ha
    obtain ⟨⟨nm, ar, body⟩, -, rfl⟩ := List.mem_map.1 ha
    left
    exact DataToWord.Proofs.comp_noShareInst dc nm 2 body _ _ rfl
  obtain ⟨hf, hr, -⟩ := compileToWordConventions2 wc asmConf _ ign _ hwc hguard
  exact labelsRel_transfer Flapjack.extractLabels _ _ hf hr hsrc

/-- Exact HOL `lab_labels_ok_oracle` (`backendProofScript.sml:1337-1419`). The
six-fold `SND` projection composed with `config_tuple2` is written with
`Prod.snd`; `syntax` is `syntaxOrac`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "lab_labels_ok_oracle"
  (words_as_type_indexed_bitvec)]
theorem labLabelsOk_oracle {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syntaxOrac : Nat → (Nat × Nat) × List AstHOL.Dec) (i : Nat)
    (cfg : LabToTarget.Config) (code : LabSem.LabProgHOL width) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') ∧
      cakeOrac asmConf c' syntaxOrac
          (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
          (fun ps => ps.labProg) i = (cfg, code) →
      StackToLab.Proofs.CodeInstalled.labelsOk code := by
  rintro ⟨h, hc⟩
  have hst := cakeOrac_stack_allDistinct asmConf c prog b bm c' syntaxOrac i h
  rw [cakeOrac_eq_pair] at hc hst
  have hcode := (Prod.mk.inj hc).2
  subst hcode
  generalize cakeConfigs asmConf c' syntaxOrac i = C at hst ⊢
  unfold compileIncProgs at hst ⊢
  simp only [keepProgs_true, id] at hst ⊢
  rcases hcw : WordToStack.Native.compileWordToStackNative asmConf C.stackConf.perfCalls
      (asmConf.regCount - (5 + asmConf.avoidRegs.length))
      (List.map (fun p => WordToWord.fullCompileSingle asmConf.twoRegArith
          (asmConf.regCount - (5 + asmConf.avoidRegs.length)) C.wordToWordConf.regAlg asmConf
          (p, none))
        (List.map (DataToWord.compilePart (Flapjack.Compiler.Backend.Backend.ensureFpConfOk
            asmConf C.dataConf))
          (BviToData.compileProg
            (BvlToBvi.bvlToBviCompileIncAll C.bvlConf
              (ClosToBvl.closToBvlCompileInc C.closConf
                (FlatToClos.incCompileDecs
                  (SourceToFlat.incCompile (syntaxOrac i).1 C.sourceConf
                    (SourceToSource.compile (syntaxOrac i).2)).2)).2).2)))
      (AppList.nil, C.wordConf.bitmapsLength) with ⟨sp, rest⟩
  simp only [hcw] at hst ⊢
  have hent := WordToStack.Native.ExtractLabelsCompiler.compileWordToStackLabPres asmConf _ _ _ _
    sp rest hcw (wordProg_labels asmConf _ _ _)
  unfold StackToLab.compileNoStubs
  refine StackToLab.Proofs.FlattenHelpers.progToSectionLabelsOk ⟨?_, ?_⟩
  · intro np hmem
    simp only [StackNames.compileHOL, List.mem_map] at hmem
    obtain ⟨q, hq, rfl⟩ := hmem
    show StackToLab.Proofs.CompileLabPres.EntryLabelsOk
      (StackNames.progCompEntryHOL C.stackConf.regNames q)
    unfold StackToLab.Proofs.CompileLabPres.EntryLabelsOk
    simp only [StackNames.progCompEntryHOL, ← StackNames.stackNamesLabPres]
    obtain ⟨q1, hq1, rfl⟩ := hq
    obtain ⟨⟨n0, p0⟩, hp0, rfl⟩ := hq1
    simp only [StackRemove.progComp, ← StackRemove.Proofs.LabPres.stackRemoveLabPres,
      StackAlloc.progComp]
    obtain ⟨hE, hD⟩ := hent _ hp0
    have := StackAlloc.stack_alloc_lab_pres n0 (StackAlloc.nextLabHOL p0 2) p0 0
      ⟨hE, hD, Nat.le_refl _⟩
    exact ⟨this.1, this.2.1⟩
  · rw [StackNames.map_fst_compileHOL, List.map_map, List.map_map]
    convert hst using 2
    funext x
    rfl

/-- The lab configuration update of one incremental step adds the section
numbers of well-labelled code (Flapjack infrastructure). -/
theorem labConf_update_domain {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (L : LabToTarget.Config) (code : LabSem.LabProgHOL width)
    (hok : StackToLab.Proofs.CodeInstalled.labelsOk code) (x : Nat)
    (hx : sptDomain ((match LabToTarget.compile asmConf L code with
      | none => id
      | some (_, c') => fun _ => c') L).labels x) :
    x ∈ {x | sptDomain L.labels x} ∪ {n | n ∈ code.map (fun sec => sec.sectionId)} := by
  have hsec := stackLabelsOk_fstCodeLabels_sectionNum _ hok
  rcases hcomp : LabToTarget.compile asmConf L code with _ | ⟨bytes, c2⟩
  · rw [hcomp] at hx
    exact .inl hx
  · rw [hcomp] at hx
    have hd := compileLab_domainLabels asmConf _ _ bytes c2 hcomp
    change sptDomain c2.labels x at hx
    rw [hd, LabToTarget.FilterSkip.getCodeLabelsFilterSkip, hsec] at hx
    rcases hx with hx | hx
    · exact .inr hx
    · exact .inl hx

/-- One oracle step adds exactly the section numbers of that step's lab code to
the label domain (Flapjack infrastructure for `accum_lab_conf_labels`). -/
theorem labConf_step {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syntaxOrac : Nat → (Nat × Nat) × List AstHOL.Dec) (i : Nat)
    (h : BackendDefs.compile asmConf c prog = some (b, bm, c')) :
    {x | sptDomain (cakeConfigs asmConf c' syntaxOrac (i + 1)).labConf.labels x} ⊆
      {x | sptDomain (cakeConfigs asmConf c' syntaxOrac i).labConf.labels x} ∪
        {n | n ∈ (compileIncProgs true asmConf (cakeConfigs asmConf c' syntaxOrac i)
          (syntaxOrac i)).2.labProg.map (fun sec => sec.sectionId)} := by
  have hok := labLabelsOk_oracle asmConf c prog b bm c' syntaxOrac i _ _ ⟨h, Prod.mk.eta.symm⟩
  rw [cakeOrac_eq_pair] at hok
  intro x hx
  change sptDomain (compileIncProgs true asmConf (cakeConfigs asmConf c' syntaxOrac i)
    (syntaxOrac i)).1.labConf.labels x at hx
  generalize cakeConfigs asmConf c' syntaxOrac i = C at hok hx ⊢
  unfold compileIncProgs at hok hx ⊢
  simp only [keepProgs_true, id] at hok hx ⊢
  exact labConf_update_domain asmConf C.labConf _ hok x hx

/-- Exact HOL `accum_lab_conf_labels` (`backendProofScript.sml:1432-1467`).
`domain` is `sptDomain`, `BIGUNION (set l)` is `⋃₀ {s | s ∈ l}`, `COUNT_LIST i`
is `List.range i`, HOL `set` of a list is its membership set; the six-fold
`SND` projection is written with `Prod.snd`; `syntax` is `syntaxOrac`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "accum_lab_conf_labels"
  (words_as_type_indexed_bitvec)]
theorem accumLabConf_labels {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syntaxOrac : Nat → (Nat × Nat) × List AstHOL.Dec) (i : Nat) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') →
      {x | sptDomain (cakeConfigs asmConf c' syntaxOrac i).labConf.labels x} ⊆
        {x | sptDomain c'.labConf.labels x} ∪
          ⋃₀ {s | s ∈ (List.range i).map ((fun l => {x | x ∈ l}) ∘
            List.map (fun sec : LabLang.Section (Line (AsmOrCbw (HolAsm width) HolMemop
              (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width)
                Flapjack.Basis.Pure.MlString.MlString) (BitVec width)) => sec.sectionId) ∘
            Prod.snd ∘
            cakeOrac asmConf c' syntaxOrac
              (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
              (fun ps => ps.labProg))} := by
  intro h
  induction i with
  | zero => exact Set.subset_union_left
  | succ i ih =>
    intro x hx
    rcases labConf_step asmConf c prog b bm c' syntaxOrac i h hx with h1 | h2
    · rcases ih h1 with h3 | ⟨s, hs, hxs⟩
      · exact .inl h3
      · refine .inr ⟨s, ?_, hxs⟩
        simp only [Set.mem_ofPred_eq, List.range_succ, List.map_append, List.mem_append] at hs ⊢
        exact .inl hs
    · refine .inr ⟨_, List.mem_map_of_mem (List.mem_range.2 (Nat.lt_succ_self i)), ?_⟩
      simp only [Function.comp_apply, cakeOrac_eq_pair]
      exact h2

/-- Exact HOL `monotonic_DISJOINT_labels_lab` (`backendProofScript.sml:1841-1872`).
`DISJOINT` is `Disjoint` on sets, `(≠)` is `fun x y => x ≠ y`, `domain` is
`sptDomain`; the six-fold `SND` projection is written with `Prod.snd`;
`syntax` is `syntaxOrac`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "monotonic_DISJOINT_labels_lab"
  (words_as_type_indexed_bitvec)]
theorem monotonic_disjointLabelsLab {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syntaxOrac : Nat → (Nat × Nat) × List AstHOL.Dec) (i : Nat) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') ∧
      oracleMonotonic ((fun l => {x | x ∈ l}) ∘
          List.map (fun sec : LabLang.Section (Line (AsmOrCbw (HolAsm width) HolMemop
            (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width)
              Flapjack.Basis.Pure.MlString.MlString) (BitVec width)) => sec.sectionId) ∘
          Prod.snd)
        (fun x y => x ≠ y) {x | sptDomain c'.labConf.labels x}
        (cakeOrac asmConf c' syntaxOrac
          (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
          (fun ps => ps.labProg)) →
      Disjoint {x | sptDomain (cakeConfigs asmConf c' syntaxOrac i).labConf.labels x}
        {x | x ∈ (cakeOrac asmConf c' syntaxOrac
          (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ configTuple2)
          (fun ps => ps.labProg) i).2.map (fun sec => sec.sectionId)} := by
  rintro ⟨h, hm⟩
  rw [Set.disjoint_left]
  intro x hx hy
  rcases accumLabConf_labels asmConf c prog b bm c' syntaxOrac i h hx with h1 | ⟨s, hs, hxs⟩
  · exact hm.2 i x x h1 hy rfl
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
    exact hm.1 j i x x (List.mem_range.1 hj) hxs hy rfl

end Flapjack.Compiler.Backend.BackendProof
