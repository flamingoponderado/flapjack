module

public import Flapjack.Compiler.Backend.LabProps.LabelExtraction
public import Flapjack.Compiler.Backend.LabProps.SecLabelOk
public import Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
public import Flapjack.Compiler.Backend.StackToLab.Proofs.CompileLabPres
public import Flapjack.Compiler.Backend.StackToLab.Compile

@[expose] public section

set_option autoImplicit false

/-! backendProofScript.sml 1309-1335 and 1469-1479: the first components of the
code labels of well-labelled lab code are exactly its section numbers, and the
section numbers of `stack_to_lab$compile` output are the program names and
stubs. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackLang

/-- Exact HOL `sec_labels_ok_FST_code_labels_Section_num`
(`backendProofScript.sml:1309-1328`). `IMAGE FST` is `Prod.fst ''`, HOL `set`
of a list is its membership set, and `EVERY` is a membership forall. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "sec_labels_ok_FST_code_labels_Section_num" (words_as_type_indexed_bitvec)]
theorem secLabelsOk_fstCodeLabels_sectionNum {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ code, secLabelsOk sec) →
      Prod.fst '' getCodeLabels code = {n | n ∈ code.map (·.sectionId)} := by
  intro hok
  rw [getCodeLabelsExtractLabels code hok, Set.image_union, Set.image_image]
  ext n
  simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, List.mem_map, List.mem_flatten]
  constructor
  · rintro (⟨sec, hsec, rfl⟩ | ⟨p, ⟨l, ⟨sec, hsec, rfl⟩, hp⟩, rfl⟩)
    · exact ⟨sec, hsec, rfl⟩
    · refine ⟨sec, hsec, ?_⟩
      have := (EVERY_sec_label_ok sec.sectionId sec.lines).2 (hok sec hsec) p hp
      exact this.1.symm
  · rintro ⟨sec, hsec, rfl⟩
    exact .inl ⟨sec, hsec, rfl⟩

/-- Exact HOL `stack_labels_ok_FST_code_labels_Section_num`
(`backendProofScript.sml:1330-1335`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "stack_labels_ok_FST_code_labels_Section_num" (words_as_type_indexed_bitvec)]
theorem stackLabelsOk_fstCodeLabels_sectionNum {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    labelsOk code →
      Prod.fst '' getCodeLabels code = {n | n ∈ code.map (·.sectionId)} := by
  intro h
  exact secLabelsOk_fstCodeLabels_sectionNum code (labelsOkImp code h).1

/-- Exact HOL `MAP_Section_num_stack_to_lab_SUBSET`
(`backendProofScript.sml:1469-1479`). HOL `set` of a list is its membership
set and `count n` is `{m | m < n}`; `labs : num -> bool` is a `Set Nat`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "MAP_Section_num_stack_to_lab_SUBSET" (words_as_type_indexed_bitvec)]
theorem mapSectionNum_stackToLab_subset {width : Nat} [NeZero width]
    (prog : List (Nat × StackLang.HolProg width)) (labs : Set Nat)
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) :
    {x | x ∈ prog.map Prod.fst} ⊆ labs ∧ {m | m < gcStubLocation + 1} ⊆ labs →
      {x | x ∈ (StackToLab.compile scc dc maxHeap sp offset prog).map (·.sectionId)} ⊆ labs := by
  rintro ⟨hp, hc⟩ x hx
  simp only [Set.mem_ofPred_eq, StackToLab.compile] at hx
  rw [StackToLab.Proofs.CodeInstalled.mapProgToSectionFst, StackNames.map_fst_compileHOL,
    StackToLab.Proofs.CompileLabPres.mapFstCompileCompile] at hx
  have hg : gcStubLocation = 4 := rfl
  simp only [List.mem_cons] at hx
  rcases hx with rfl | rfl | rfl | rfl | hx
  · exact hc (show (0:Nat) < gcStubLocation + 1 by omega)
  · exact hc (show (1:Nat) < gcStubLocation + 1 by omega)
  · exact hc (show (2:Nat) < gcStubLocation + 1 by omega)
  · exact hc (show gcStubLocation < gcStubLocation + 1 by omega)
  · exact hp hx

end Flapjack.Compiler.Backend.BackendProof
