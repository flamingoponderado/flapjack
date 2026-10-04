import Flapjack.Pancake.Proofs.PanToTarget.InitHelpers
import Flapjack.Pancake.Proofs.PanToTarget.WordToWordNoInstall
import Flapjack.Pancake.Proofs.PanToWord
import Flapjack.Pancake.Proofs.PanToWord.LabPres
import Flapjack.Pancake.Proofs.PanToWord.NoInstallCode
import Flapjack.Compiler.Backend.Proofs.WordConventions
import Flapjack.Compiler.Backend.WordToStack.Proofs.ExtractLabelsCompiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackConventions
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstallTop
import Flapjack.Compiler.Backend.StackToLab.Proofs.CompileLabPres
import Flapjack.Compiler.Backend.StackToLab.Proofs.NoInstall
import Flapjack.Compiler.Backend.StackToLab.Proofs.GoodCode
import Flapjack.Compiler.Backend.Backend

/-!
# `pan_to_targetProof`: labels, `good_code` and `no_install` of the compiled stack/lab code

`pan_to_stack_first_ALL_DISTINCT` (89-114), `pan_to_stack_compile_lab_pres` (116-175),
`pan_to_lab_labels_ok` (177-191), `word_to_stack_good_code_lemma` (193-247) and
`from_pan_to_lab_no_install` (1169-1191) of
`cakeml/pancake/proofs/pan_to_targetProofScript.sml`. The script's overloads
`pan_to_word_compile_prog`, `word_to_word_compile`, `word_to_stack_compile` and
`stack_to_lab_compile` are the tagged `panToWordCompileProgHOL`, `WordToWord.compile`,
`WordToStack.Native.compileNative` and `StackToLab.compile`; `F` is `false`.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget
open Flapjack Flapjack.Pancake.PanLang Flapjack.Compiler.Encoders.Asm Flapjack.WordConvs

/-- Per-row label facts carry over `labels_rel` between programs with the same names
    (Flapjack infrastructure; the `EVERY2` step of HOL's `pan_to_stack_compile_lab_pres`). -/
theorem labels_of_labelsRel {width : Nat} [NeZero width] :
    ∀ (A B : List (Nat × Nat × WordLangProgHOL (BitVec width))),
      B.map Prod.fst = A.map Prod.fst →
      List.Forall₂ labelsRel (A.map (fun p => extractLabels p.2.2))
        (B.map (fun p => extractLabels p.2.2)) →
      (∀ r ∈ A, (∀ q ∈ extractLabels r.2.2, q.1 = r.1 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1) ∧
        (extractLabels r.2.2).Nodup) →
      ∀ r ∈ B, (∀ q ∈ extractLabels r.2.2, q.1 = r.1 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1) ∧
        (extractLabels r.2.2).Nodup
  | [], [], _, _, _ => by simp
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | a :: A, b :: B, hn, hr, hA => by
      simp only [List.map_cons, List.cons.injEq] at hn
      simp only [List.map_cons, List.forall₂_cons] at hr
      obtain ⟨⟨hnd, hsub⟩, hrest⟩ := hr
      intro r hr'
      rcases List.mem_cons.mp hr' with rfl | hr'
      · obtain ⟨ha1, ha2⟩ := hA a (List.mem_cons_self ..)
        refine ⟨fun q hq => ?_, hnd ha2⟩
        have := ha1 q (hsub q hq)
        rw [hn.1]
        exact this
      · exact labels_of_labelsRel A B hn.2 hrest (fun r hr => hA r (List.mem_cons_of_mem _ hr)) r hr'

/-- HOL `pan_to_stack_first_ALL_DISTINCT` (`pan_to_targetProofScript.sml:89-114`). HOL's free
    `mc pan_code wprog0 c col wprog bitmaps c'' fs p` are explicit. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "pan_to_stack_first_ALL_DISTINCT"
  (words_as_type_indexed_bitvec)]
theorem pan_to_stack_first_ALL_DISTINCT {width : Nat} [NeZero width] {State Projection : Type}
    (mc : MachineConfig width State Projection) (panCode : List (DeclHOL width))
    (wprog0 : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (c : Compiler.Backend.Backend.Config) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (c'' : Compiler.Backend.WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × Compiler.Backend.StackLang.HolProg width)) :
    panToWordCompileProgHOL mc.target.config.isa panCode = wprog0 ∧
      Compiler.Backend.WordToWord.compile c.wordToWordConf mc.target.config wprog0 = (col, wprog) ∧
      mc.target.config.isa ≠ .ag32 ∧
      Compiler.Backend.WordToStack.Native.compileNative mc.target.config false wprog =
        (bitmaps, c'', fs, p) ∧
      ((functionsHOL panCode).map Prod.fst).Nodup →
    (p.map Prod.fst).Nodup := by
  rintro ⟨h0, hw, hisa, hs, hd⟩
  have hd0 := panToWordFirstCompileProgAllDistinctHOL mc.target.config.isa panCode hd
  rw [h0] at hd0
  obtain ⟨hfst, -⟩ := Compiler.Backend.BackendProof.compileToWordConventions2 _ _ wprog0 col wprog hw
    (fun _ _ => .inr hisa)
  have hmin := PanToWord.pan_to_word_compile_prog_lab_min _ panCode wprog0 h0
  rw [word_to_stack_compile_FST mc wprog bitmaps c'' fs p hs, hfst]
  have big : ∀ x ∈ wprog0.map Prod.fst, 60 ≤ x := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact hmin q hq
  simp only [List.nodup_cons, List.mem_cons, not_or]
  refine ⟨⟨by decide, fun h => ?_⟩, fun h => ?_, hd0⟩
  · have := big _ h; simp [raiseStubLocation, wordNumStubs, stackNumStubs] at this
  · have := big _ h; simp [storeConstsStubLocation, wordNumStubs, stackNumStubs] at this

/-- HOL `pan_to_stack_compile_lab_pres` (`pan_to_targetProofScript.sml:116-175`). HOL's free
    variables are explicit as in `pan_to_stack_first_ALL_DISTINCT`; `extract_labels` on the
    stack programs is the tagged stackProps `extractLabels`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "pan_to_stack_compile_lab_pres"
  (words_as_type_indexed_bitvec)]
theorem pan_to_stack_compile_lab_pres {width : Nat} [NeZero width] {State Projection : Type}
    (mc : MachineConfig width State Projection) (panCode : List (DeclHOL width))
    (wprog0 : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (c : Compiler.Backend.Backend.Config) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (c'' : Compiler.Backend.WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × Compiler.Backend.StackLang.HolProg width)) :
    panToWordCompileProgHOL mc.target.config.isa panCode = wprog0 ∧
      Compiler.Backend.WordToWord.compile c.wordToWordConf mc.target.config wprog0 = (col, wprog) ∧
      mc.target.config.isa ≠ .ag32 ∧
      Compiler.Backend.WordToStack.Native.compileNative mc.target.config false wprog =
        (bitmaps, c'', fs, p) ∧
      ((functionsHOL panCode).map Prod.fst).Nodup →
    (p.map Prod.fst).Nodup ∧
      (∀ n ∈ p.map Prod.fst, n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ Compiler.Backend.StackLang.gcStubLocation) ∧
      (∀ np ∈ p,
        (∀ l ∈ StackPropsCodeLabels.extractLabels np.2, l.1 = np.1 ∧ l.2 ≠ 0 ∧ l.2 ≠ 1) ∧
          (StackPropsCodeLabels.extractLabels np.2).Nodup) := by
  rintro ⟨h0, hw, hisa, hs, hd⟩
  have hfirst := pan_to_stack_first_ALL_DISTINCT mc panCode wprog0 c col wprog bitmaps c'' fs p
    ⟨h0, hw, hisa, hs, hd⟩
  obtain ⟨hfst, hrel, -⟩ := Compiler.Backend.BackendProof.compileToWordConventions2 _ _ wprog0 col
    wprog hw (fun _ _ => .inr hisa)
  have src := labels_of_labelsRel wprog0 wprog hfst hrel
    (PanToWord.pan_to_word_compile_lab_pres _ panCode wprog0 h0)
  have hlp := Compiler.Backend.WordToStack.Native.ExtractLabelsCompiler.wordToStackCompileLabPres
    mc.target.config wprog src
  dsimp only at hlp
  rw [hs] at hlp
  have hmin := PanToWord.pan_to_word_compile_prog_lab_min _ panCode wprog0 h0
  refine ⟨hfirst, fun n hn => ?_, hlp.2⟩
  rw [hlp.1, hfst] at hn
  simp only [List.mem_cons, List.mem_map] at hn
  rcases hn with rfl | rfl | ⟨q, hq, rfl⟩
  · decide
  · decide
  · have := hmin q hq
    simp only [Compiler.Backend.StackLang.gcStubLocation, stackNumStubs]
    omega

/-- HOL `pan_to_lab_labels_ok` (`pan_to_targetProofScript.sml:177-191`). HOL's free
    `max_heap sp lprog` follow the variables of `pan_to_stack_compile_lab_pres`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "pan_to_lab_labels_ok"
  (words_as_type_indexed_bitvec)]
theorem pan_to_lab_labels_ok {width : Nat} [NeZero width] {State Projection : Type}
    (mc : MachineConfig width State Projection) (panCode : List (DeclHOL width))
    (wprog0 : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (c : Compiler.Backend.Backend.Config) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (c'' : Compiler.Backend.WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × Compiler.Backend.StackLang.HolProg width)) (maxHeap sp : Nat)
    (lprog : Compiler.Backend.LabSem.LabProgHOL width) :
    panToWordCompileProgHOL mc.target.config.isa panCode = wprog0 ∧
      Compiler.Backend.WordToWord.compile c.wordToWordConf mc.target.config wprog0 = (col, wprog) ∧
      mc.target.config.isa ≠ .ag32 ∧
      Compiler.Backend.WordToStack.Native.compileNative mc.target.config false wprog =
        (bitmaps, c'', fs, p) ∧
      Compiler.Backend.StackToLab.compile c.stackConf c.dataConf maxHeap sp
        mc.target.config.addrOffset p = lprog ∧
      ((functionsHOL panCode).map Prod.fst).Nodup →
    Compiler.Backend.StackToLab.Proofs.CodeInstalled.labelsOk lprog := by
  rintro ⟨h0, hw, hisa, hs, hl, hd⟩
  obtain ⟨h1, h2, h3⟩ := pan_to_stack_compile_lab_pres mc panCode wprog0 c col wprog bitmaps c''
    fs p ⟨h0, hw, hisa, hs, hd⟩
  rw [← hl]
  exact Compiler.Backend.StackToLab.Proofs.CompileLabPres.stackToLabCompileLabPres ⟨h2, h3, h1⟩

/-- HOL `word_to_stack_good_code_lemma` (`pan_to_targetProofScript.sml:193-247`). HOL's free
    `c mc pan_code col wprog bitmaps c'' fs p` are explicit; `good_code` is the tagged
    stack_to_labProof `good_code_def`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "word_to_stack_good_code_lemma"
  (words_as_type_indexed_bitvec)]
theorem word_to_stack_good_code_lemma {width : Nat} [NeZero width] {State Projection : Type}
    (c : Compiler.Backend.Backend.Config) (mc : MachineConfig width State Projection)
    (panCode : List (DeclHOL width)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (c'' : Compiler.Backend.WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × Compiler.Backend.StackLang.HolProg width)) :
    Compiler.Backend.WordToWord.compile c.wordToWordConf mc.target.config
        (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog) ∧
      mc.target.config.isa ≠ .ag32 ∧
      Compiler.Backend.WordToStack.Native.compileNative mc.target.config false wprog =
        (bitmaps, c'', fs, p) ∧
      mc.target.config.avoidRegs.length + 13 ≤ mc.target.config.regCount ∧
      ((functionsHOL panCode).map Prod.fst).Nodup →
    Compiler.Backend.StackToLab.Proofs.GoodCode.goodCode
      (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)) p := by
  rintro ⟨hw, hisa, hs, hregs, hd⟩
  have lab := pan_to_stack_compile_lab_pres mc panCode _ c col wprog bitmaps c'' fs p
    ⟨rfl, hw, hisa, hs, hd⟩
  obtain ⟨hfst, -, hout⟩ := Compiler.Backend.BackendProof.compileToWordConventions2 _ _ _ col
    wprog hw (fun _ _ => .inr hisa)
  have hpost : (wprog.all fun row => postAllocConventionsHOL
      (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) row.2.2) = true :=
    List.all_eq_true.mpr fun row hr => (hout row hr).2.1
  obtain ⟨halloc, hreg, hcall⟩ := WordToStackProofs.StackConventions.wordToStackStackConvs
    mc.target.config wprog bitmaps c'' fs p _ hs hpost rfl (by omega)
  have hk : mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length) + 2 =
      mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3) := by omega
  rw [hk] at hreg
  have hmin := PanToWord.pan_to_word_compile_prog_lab_min mc.target.config.isa panCode
    (panToWordCompileProgHOL mc.target.config.isa panCode) rfl
  have hnames := word_to_stack_compile_FST mc wprog bitmaps c'' fs p hs
  refine ⟨lab.1, fun kp hkp => ⟨?_, halloc kp.2 (List.mem_map_of_mem hkp)⟩, hcall, hreg, lab.2.2⟩
  have hk1 : kp.1 ∈ p.map Prod.fst := List.mem_map_of_mem hkp
  rw [hnames, hfst] at hk1
  simp only [List.mem_cons, List.mem_map] at hk1
  rcases hk1 with h | h | ⟨q, hq, h⟩
  · rw [h]; decide
  · rw [h]; decide
  · rw [← h]
    have := hmin q hq
    simp only [stackNumStubs]
    omega

/-- HOL `from_pan_to_lab_no_install` (`pan_to_targetProofScript.sml:1169-1191`). HOL's free
    `pan_code ac isa wprog0 wc col wprog bm c fs p scc dc lim regc off` are explicit (the Pancake
    program is compiled for an arbitrary `isa`, independent of `ac.ISA`), and `no_install` on lab
    programs is the tagged labProps `noInstall`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "from_pan_to_lab_no_install"
  (words_as_type_indexed_bitvec)]
theorem from_pan_to_lab_no_install {width : Nat} [NeZero width] (panCode : List (DeclHOL width))
    (ac : AsmConfigExact width) (isa : AsmArchitecture)
    (wprog0 : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (wc : Compiler.Backend.WordToWord.Config) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bm : List (BitVec width))
    (c : Compiler.Backend.WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × Compiler.Backend.StackLang.HolProg width))
    (scc : Compiler.Backend.StackToLab.Config) (dc : Compiler.Backend.DataToWord.Config)
    (lim regc : Nat) (off : BitVec width × BitVec width) :
    ((functionsHOL panCode).map Prod.fst).Nodup ∧ ac.isa ≠ .ag32 ∧
      panToWordCompileProgHOL isa panCode = wprog0 ∧
      Compiler.Backend.WordToWord.compile wc ac wprog0 = (col, wprog) ∧
      Compiler.Backend.WordToStack.Native.compileNative ac false wprog = (bm, c, fs, p) →
    Compiler.Backend.LabProps.noInstall (Compiler.Backend.StackToLab.compile scc dc lim regc off p) := by
  rintro ⟨hd, hisa, h0, hw, hs⟩
  have hd0 := panToWordFirstCompileProgAllDistinctHOL isa panCode hd
  rw [h0] at hd0
  have hni0 := PanToWord.pan_to_word_compile_prog_no_install_code isa panCode wprog0 h0
  have hnm0 := PanToWord.pan_to_word_compile_prog_no_mt_code isa panCode wprog0 h0
  obtain ⟨hni, -⟩ := Flapjack.PanToTarget.word_to_word_compile_no_install_no_alloc wc ac wprog0 col
    wprog ⟨hw, hd0, hnm0, hni0⟩
  obtain ⟨hfst, -⟩ := Compiler.Backend.BackendProof.compileToWordConventions2 wc ac wprog0 col wprog
    hw (fun _ _ => .inr hisa)
  have hd1 : (wprog.map Prod.fst).Nodup := hfst ▸ hd0
  have hall := Compiler.Backend.WordToStack.Native.wordToStackCompileNoInstall ac wprog bm c fs p
    hd1 hni hs
  exact Compiler.Backend.StackToLab.Proofs.NoInstall.compileNoInstall p _
    ⟨fun ap h => List.all_eq_true.mp hall ap h, rfl⟩

end Flapjack.Pancake.Proofs.PanToTarget
