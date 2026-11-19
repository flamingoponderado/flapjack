module

public import Flapjack.Compiler.Backend.LabToTarget.FilterSkip
public import Flapjack.Compiler.Backend.LabToTarget.CodeSafety

@[expose] public section

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- Full original safety-disjunction preservation. Both source alternatives
and every FFI-name witness remain unchanged; actual Install fetches pull back
to the unfiltered program. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "no_install_or_no_share_mem_filter_skip"
  (words_as_type_indexed_bitvec)]
theorem noInstallOrNoShareMemFilterSkip {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) (ffiNames : List HolFfiName) :
    noInstallOrNoShareMem code ffiNames → noInstallOrNoShareMem (filterSkip code) ffiNames := by
  rintro (⟨hno,hffi⟩ | hno)
  · exact Or.inl ⟨(noShareMemFilterSkip code).mpr hno,hffi⟩
  · apply Or.inr
    intro p position bytes len hfetch
    obtain ⟨originalPc,horiginal⟩ := asmFetchAuxFilterSkip code p
      (.labAsm .install position bytes len) ⟨hfetch,rfl⟩
    exact hno originalPc position bytes len horiginal

/-- Flapjack infrastructure for `sec_labels_ok_filter_skip`: a line removed by
`not_skip` is not a label, so it satisfies `sec_label_ok` trivially. HOL
discharges the same step by `EVAL_TAC` after the per-line case split. -/
private theorem secLabelOk_of_notSkip_false {width : Nat} [NeZero width] (id : Nat)
    (line : LabLineHOL width) (h : notSkip line = false) : secLabelOk id line := by
  cases line with
  | label s l len => simp [notSkip] at h
  | labAsm a w bytes len => simp [notSkip] at h
  | asm a bytes len =>
      cases a with
      | asmi i =>
          cases i with
          | inst x => cases x <;> simp [notSkip, secLabelOk] at h ⊢
          | _ => simp [notSkip] at h
      | cbw l r => simp [notSkip] at h
      | shareMem op r a => simp [notSkip] at h

/-- Exact HOL `sec_labels_ok_filter_skip` (`lab_to_targetProofScript.sml:3601-3612`):
skipping no-op instructions preserves label well-formedness of the whole
program. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_labels_ok_filter_skip"
  (words_as_type_indexed_bitvec)]
theorem secLabelsOk_filterSkip {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) :
    (∀ sec ∈ filterSkip code, secLabelsOk sec) ↔
      (∀ sec ∈ code, secLabelsOk sec) := by
  induction code with
  | nil => simp [filterSkip]
  | cons sec rest ih =>
      rcases sec with ⟨id, lines⟩
      have hsec : secLabelsOk (⟨id, lines.filter notSkip⟩ : LabSectionHOL width) ↔
          secLabelsOk (⟨id, lines⟩ : LabSectionHOL width) := by
        constructor
        · intro h line hline
          by_cases hf : notSkip line = true
          · exact h line (List.mem_filter.mpr ⟨hline, hf⟩)
          · exact secLabelOk_of_notSkip_false id line (by
              cases hb : notSkip line <;> simp_all)
        · intro h line hline
          exact h line (List.mem_filter.mp hline).1
      simp only [filterSkip, List.forall_mem_cons]
      rw [hsec, ih]

end Flapjack.Compiler.Backend.LabToTarget
