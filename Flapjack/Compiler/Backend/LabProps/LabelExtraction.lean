module

public import Flapjack.Compiler.Backend.LabProps.LabelSets
public import Flapjack.Compiler.Backend.LabProps.Labels
public import Mathlib.Data.Set.Lattice

@[expose] public section

/-! `labPropsScript.sml` label-extraction set facts. The HOL proofs use
`BIGUNION`/`IMAGE`/`set`, so the set lattice lives in this leaf beneath the
`LabProps` counterpart rather than in the `LabelSets` hub. -/

namespace Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Exact HOL `line_get_code_labels_extract_labels` (`labPropsScript.sml:1288`):
the union of every listed line's code-label set is the second component of the
extracted label list. HOL proves it by `recInduct extract_labels_ind`; the Lean
induction is over the same list recursion, with the hypothesis restated in
membership form so the per-line case splits close directly. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml"
  "line_get_code_labels_extract_labels" (words_as_type_indexed_bitvec)]
theorem lineGetCodeLabels_extractLabels {width : Nat} [NeZero width]
    (l : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    ⋃₀ (lineGetCodeLabels '' {line | line ∈ l}) =
      (Prod.snd '' {p | p ∈ extractLabels l}) := by
  induction l with
  | nil =>
    ext p
    simp [extractLabels]
  | cons line xs ih =>
    have ih' : ∀ p : Nat, (∃ x ∈ xs, p ∈ lineGetCodeLabels x) ↔
        (∃ q ∈ extractLabels xs, q.2 = p) := by
      intro p
      have h := congrArg (fun s : Set Nat => p ∈ s) ih
      simpa [Set.mem_sUnion, Set.mem_image] using h
    simp only [lineGetCodeLabels] at ih'
    ext p
    cases line with
    | label l1 l2 len =>
      simp [extractLabels, lineGetCodeLabels, Set.mem_image, ih', eq_comm]
    | asm b bytes len =>
      simp [extractLabels, lineGetCodeLabels, Set.mem_image, ih']
    | labAsm a w bytes len =>
      simp [extractLabels, lineGetCodeLabels, Set.mem_image, ih']

/-- Flapjack-only bridge (no HOL declaration): a label line in the section list
    contributes its own `(sectionId, label)` pair to `extractLabels`. -/
theorem memExtractLabelsOfLabel {width : Nat} [NeZero width] :
    ∀ (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
        (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (a b len : Nat),
      Line.label a b len ∈ lines → (a, b) ∈ extractLabels lines := by
  intro lines
  induction lines with
  | nil =>
    intro a b len h
    simp at h
  | cons line rest ih =>
    intro a b len h
    cases line with
    | label l1 l2 len' =>
      simp only [List.mem_cons, Line.label.injEq] at h
      rcases h with ⟨rfl, rfl, _⟩ | h
      · simp [extractLabels]
      · simp only [extractLabels, List.mem_cons]
        exact Or.inr (ih a b len h)
    | asm instruction bytes len' =>
      simp only [extractLabels]
      have h' : Line.label a b len ∈ rest := by
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      exact ih a b len h'
    | labAsm instruction word bytes len' =>
      simp only [extractLabels]
      have h' : Line.label a b len ∈ rest := by
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      exact ih a b len h'

/-- Flapjack-only bridge (no HOL declaration): every extracted pair comes from
    a label line of the same section list. -/
theorem memLabelOfExtractLabels {width : Nat} [NeZero width]
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (a b : Nat) :
    (a, b) ∈ extractLabels lines → ∃ len, Line.label a b len ∈ lines := by
  induction lines with
  | nil =>
    intro h
    simp [extractLabels] at h
  | cons line rest ih =>
    intro h
    cases line with
    | label l1 l2 len =>
      simp only [extractLabels, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨len, by simp⟩
      · obtain ⟨len', hlen'⟩ := ih h
        exact ⟨len', List.mem_cons_of_mem _ hlen'⟩
    | asm instruction bytes len =>
      simp only [extractLabels] at h
      obtain ⟨len', hlen'⟩ := ih h
      exact ⟨len', List.mem_cons_of_mem _ hlen'⟩
    | labAsm instruction word bytes len =>
      simp only [extractLabels] at h
      obtain ⟨len', hlen'⟩ := ih h
      exact ⟨len', List.mem_cons_of_mem _ hlen'⟩

/-- Flapjack-only lemma on the tagged `secGetCodeLabels`: under the source
    `sec_labels_ok` guard the section's label set is its own `(sectionId, 0)`
    plus the extracted label pairs. This is the section-level step HOL derives
    inline in `get_code_labels_extract_labels`. -/
theorem secGetCodeLabelsEqExtractLabels {width : Nat} [NeZero width]
    (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (hok : secLabelsOk sec) :
    secGetCodeLabels sec = {(sec.sectionId, 0)} ∪ {p | p ∈ extractLabels sec.lines} := by
  ext p
  constructor
  · intro hp
    rcases hp with h0 | ⟨n2, hmem, hlabel⟩
    · exact Or.inl h0
    · obtain ⟨line, hline, hn2⟩ := hmem
      cases line with
      | label sid lid len =>
        simp only [lineGetCodeLabels, Set.mem_singleton_iff] at hn2
        obtain ⟨rfl, _⟩ := hok (.label sid lid len) hline
        refine Or.inr ?_
        rw [hlabel, hn2]
        exact memExtractLabelsOfLabel sec.lines sec.sectionId lid len hline
      | asm instruction bytes len => simp [lineGetCodeLabels] at hn2
      | labAsm instruction word bytes len => simp [lineGetCodeLabels] at hn2
  · intro hp
    rcases hp with h0 | hmem
    · exact Or.inl h0
    · obtain ⟨len, hlen⟩ := memLabelOfExtractLabels sec.lines p.1 p.2 hmem
      obtain ⟨hpid, _⟩ := hok (.label p.1 p.2 len) hlen
      refine Or.inr ⟨p.2, ⟨.label p.1 p.2 len, hlen, ?_⟩, ?_⟩
      · simp [lineGetCodeLabels]
      · rw [← hpid]

/-- Exact HOL `get_code_labels_extract_labels` (`labPropsScript.sml:1298`):
under `EVERY sec_labels_ok code`, the program's label set is every section's
`(Section_num, 0)` pair plus the flattened extracted labels. HOL's
`LIST_TO_SET_FLAT` and `sec_label_ok_extract_labels` steps are the two helpers
above and the tagged `secLabelOk_extractLabels`. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml"
  "get_code_labels_extract_labels" (words_as_type_indexed_bitvec)]
theorem getCodeLabelsExtractLabels {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ code, secLabelsOk sec) →
    getCodeLabels code =
      (fun sec => (sec.sectionId, 0)) '' {sec | sec ∈ code} ∪
      {p | p ∈ ((code.map (fun sec => extractLabels sec.lines)).flatten)} := by
  induction code with
  | nil =>
    intro _
    ext p
    simp [getCodeLabels]
  | cons sec rest ih =>
    intro hok
    have hokrest : ∀ s ∈ rest, secLabelsOk s :=
      fun s hs => hok s (List.mem_cons_of_mem _ hs)
    have hsec := secGetCodeLabelsEqExtractLabels sec (hok sec (by simp))
    have himg : (fun s : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
        (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) => (s.sectionId, 0)) ''
        {s | s ∈ sec :: rest} =
        {(sec.sectionId, 0)} ∪ (fun s => (s.sectionId, 0)) '' {s | s ∈ rest} := by
      ext q
      simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_cons, Set.mem_union,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨s, hs, rfl⟩
        rcases hs with hs | hs
        · left
          rw [hs]
        · exact Or.inr ⟨s, hs, rfl⟩
      · rintro (h | ⟨s, hs, rfl⟩)
        · exact ⟨sec, Or.inl rfl, h.symm⟩
        · exact ⟨s, Or.inr hs, rfl⟩
    have hflat : {p | p ∈ ((sec :: rest).map (fun s => extractLabels s.lines)).flatten} =
        {p | p ∈ extractLabels sec.lines} ∪
          {p | p ∈ ((rest.map (fun s => extractLabels s.lines)).flatten)} := by
      simp only [List.map_cons, List.flatten_cons, List.mem_append]
      rw [Set.ofPred_or]
    rw [getCodeLabels_cons, ih hokrest, hsec, himg, hflat]
    ac_rfl

end Flapjack.Compiler.Backend.LabProps.LabelSets
