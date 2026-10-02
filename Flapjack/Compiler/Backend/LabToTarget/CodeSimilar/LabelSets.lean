import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar
import Flapjack.Compiler.Backend.LabProps.LabelSets

/-! Full source code-similarity preservation laws for section numbers,
ordered extracted labels, label references and defined code labels. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Flapjack membership-form BIGUNION transport, derived from the list relation. -/
private theorem relatedUnions {α β : Type} {r : α → α → Prop} (f : α → Set β)
    (preserves : ∀ x y, r x y → f x = f y) {xs ys : List α}
    (h : LinesRel r xs ys) :
    {p | ∃ x ∈ xs, p ∈ f x} = {p | ∃ y ∈ ys, p ∈ f y} := by
  induction h with
  | nil => rfl
  | cons h _ ih =>
    ext p
    have hi := Set.ext_iff.mp ih p
    simpa only [Set.mem_ofPred_eq, List.mem_cons, exists_eq_or_imp,
      preserves _ _ h] using or_congr Iff.rfl hi

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_MAP_Section_num"
  (words_as_type_indexed_bitvec)]
theorem codeSimilar_sectionNumbers {width : Nat} [NeZero width]
    (c1 c2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : codeSimilar c1 c2 →
    c1.map Section.sectionId = c2.map Section.sectionId := by
  induction c1 generalizing c2 with
  | nil => cases c2 <;> simp [codeSimilar]
  | cons sec rest ih =>
    cases c2 with
    | nil => simp [codeSimilar]
    | cons sec' rest' =>
      intro h
      simp only [List.map_cons, h.2.2, ih rest' h.1]

private theorem similarExtracted {width : Nat} [NeZero width]
    {xs ys : List (LabLineHOL width)} (h : LinesRel lineSimilar xs ys) :
    extractLabels xs = extractLabels ys := by
  induction h with
  | nil => rfl
  | @cons x y xs ys h _ ih =>
    cases x <;> cases y <;> simp only [lineSimilar] at h <;> try contradiction
    all_goals simp [extractLabels, ih, h]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_extract_labels"
  (words_as_type_indexed_bitvec)]
theorem codeSimilar_extractedLabels {width : Nat} [NeZero width]
    (c1 c2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : codeSimilar c1 c2 →
    c1.map (fun sec => extractLabels sec.lines) =
      c2.map (fun sec => extractLabels sec.lines) := by
  induction c1 generalizing c2 with
  | nil => cases c2 <;> simp [codeSimilar]
  | cons sec rest ih =>
    cases c2 with
    | nil => simp [codeSimilar]
    | cons sec' rest' =>
      intro h
      simp only [List.map_cons, similarExtracted h.2.1, ih rest' h.1]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_line_get_code_labels"
  (words_as_type_indexed_bitvec)]
theorem lineSimilar_codeLabels {width : Nat} [NeZero width]
    (l1 l2 : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : lineSimilar l1 l2 →
    lineGetCodeLabels l1 = lineGetCodeLabels l2 := by
  cases l1 <;> cases l2 <;> simp only [lineSimilar] <;> intro h <;> try contradiction
  all_goals simp [lineGetCodeLabels, h]

private theorem similarSectionCodeLabels {width : Nat} [NeZero width]
    (s1 s2 : Section (LabLineHOL width))
    (h : LinesRel lineSimilar s1.lines s2.lines) (hid : s1.sectionId = s2.sectionId) :
    secGetCodeLabels s1 = secGetCodeLabels s2 := by
  have hu := relatedUnions lineGetCodeLabels lineSimilar_codeLabels h
  unfold secGetCodeLabels
  rw [hid]
  apply congrArg (fun labels : Set (Nat × Nat) => {(s2.sectionId,0)} ∪ labels)
  ext pair
  have hm (n : Nat) : (∃ line ∈ s1.lines, n ∈ lineGetCodeLabels line) ↔
      (∃ line ∈ s2.lines, n ∈ lineGetCodeLabels line) := Set.ext_iff.mp hu n
  simp only [Set.mem_ofPred_eq]
  simp_rw [hm]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_get_code_labels"
  (words_as_type_indexed_bitvec)]
theorem codeSimilar_codeLabels {width : Nat} [NeZero width]
    (c1 c2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : codeSimilar c1 c2 →
    getCodeLabels c1 = getCodeLabels c2 := by
  induction c1 generalizing c2 with
  | nil => cases c2 <;> simp [codeSimilar]
  | cons sec rest ih =>
    cases c2 with
    | nil => simp [codeSimilar]
    | cons sec' rest' =>
      intro h
      rw [getCodeLabels_cons, getCodeLabels_cons,
        similarSectionCodeLabels sec sec' h.2.1 h.2.2, ih rest' h.1]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_line_get_labels"
  (words_as_type_indexed_bitvec)]
theorem lineSimilar_labels {width : Nat} [NeZero width]
    (l1 l2 : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : lineSimilar l1 l2 →
    lineGetLabels l1 = lineGetLabels l2 := by
  cases l1 <;> cases l2 <;> simp only [lineSimilar] <;> intro h <;> try contradiction
  all_goals simp [lineGetLabels, h]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_get_labels"
  (words_as_type_indexed_bitvec)]
theorem codeSimilar_labels {width : Nat} [NeZero width]
    (c1 c2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : codeSimilar c1 c2 →
    getLabels c1 = getLabels c2 := by
  induction c1 generalizing c2 with
  | nil => cases c2 <;> simp [codeSimilar]
  | cons sec rest ih =>
    cases c2 with
    | nil => simp [codeSimilar]
    | cons sec' rest' =>
      intro h
      have hu : secGetLabels sec = secGetLabels sec' :=
        relatedUnions lineGetLabels lineSimilar_labels h.2.1
      rw [getLabels_cons, getLabels_cons, hu, ih rest' h.1]

end Flapjack.Compiler.Backend.LabToTarget
