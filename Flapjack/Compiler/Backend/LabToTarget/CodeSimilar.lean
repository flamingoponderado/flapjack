import Flapjack.Compiler.Backend.LabProps.Labels
import Flapjack.Compiler.Backend.LabSem.Classifier

/-! Original Lab-to-Target code similarity: encoding bytes, recorded lengths,
and resolved word positions may change; instructions and section/label names
must agree. Native payload carriers retain HOL's fixed byte widths and mlstring.
The original `α line` / `α sec` types have one shared HOL word-index parameter;
they do not quantify independent instruction, comparison, memory-operation or
name carriers. See scripts/hol-probes/lab_to_target_navigation_types.txt for
the inferred relation, navigation and nested constructor types.
-/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabProps

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_def"
  (words_as_type_indexed_bitvec)]
def lineSimilar {width : Nat} [NeZero width] (left right : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : Prop :=
  match left, right with
  | .label s l _, .label s' l' _ => s = s' ∧ l = l'
  | .asm a _ _, .asm a' _ _ => a = a'
  | .labAsm a _ _ _, .labAsm a' _ _ _ => a = a'
  | _, _ => False

/-- Constructor-for-constructor list relation infrastructure; the HOL EVERY2
operator has these empty and cons clauses. No new HOL declaration is claimed. -/
inductive LinesRel {α : Type} (relation : α → α → Prop) : List α → List α → Prop where
  | nil : LinesRel relation [] []
  | cons {x y xs ys} : relation x y → LinesRel relation xs ys →
      LinesRel relation (x :: xs) (y :: ys)

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_def"
  (words_as_type_indexed_bitvec)]
def codeSimilar {width : Nat} [NeZero width] (left right : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Prop :=
  match left, right with
  | [], [] => True
  | a :: as, b :: bs =>
      codeSimilar as bs ∧ LinesRel lineSimilar a.lines b.lines ∧ a.sectionId = b.sectionId
  | _, _ => False

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_sym"
  (words_as_type_indexed_bitvec)]
theorem lineSimilar_sym {width : Nat} [NeZero width] (left right : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineSimilar left right → lineSimilar right left := by
  cases left <;> cases right <;> simp only [lineSimilar] <;> intro h
  all_goals first | exact h.elim | exact h.symm | exact ⟨h.1.symm, h.2.symm⟩

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_refl"
  (words_as_type_indexed_bitvec)]
theorem lineSimilar_refl {width : Nat} [NeZero width] (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineSimilar line line := by
  cases line <;> simp [lineSimilar]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_trans"
  (words_as_type_indexed_bitvec)]
theorem lineSimilar_trans {width : Nat} [NeZero width] (x y z : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineSimilar x y ∧ lineSimilar y z → lineSimilar x z := by
  cases x <;> cases y <;> cases z <;> simp only [lineSimilar] <;> intro h <;>
    rcases h with ⟨hxy, hyz⟩ <;> try contradiction
  all_goals first | exact hxy.trans hyz | exact ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_refl"
  (words_as_type_indexed_bitvec)]
theorem codeSimilar_refl {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    codeSimilar code code := by
  induction code with
  | nil => trivial
  | cons sec rest ih =>
    refine ⟨ih, ?_, rfl⟩
    induction sec.lines with
    | nil => exact .nil
    | cons line lines ih => exact .cons (lineSimilar_refl line) ih

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_nil"
  (words_as_type_indexed_bitvec)]
theorem codeSimilar_nil {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (codeSimilar [] code ↔ code = []) ∧ (codeSimilar code [] ↔ code = []) := by
  cases code <;> simp [codeSimilar]

/-- Local list-relation infrastructure, with no independent HOL declaration. -/
private theorem similarLines_sym {width : Nat} [NeZero width]
    {left right : List (LabSem.LabLineHOL width)}
    (h : LinesRel lineSimilar left right) : LinesRel lineSimilar right left := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (lineSimilar_sym _ _ h) ih

/-- Local list-relation infrastructure, with no independent HOL declaration. -/
private theorem similarLines_trans {width : Nat} [NeZero width]
    {x y z : List (LabSem.LabLineHOL width)}
    (hxy : LinesRel lineSimilar x y) (hyz : LinesRel lineSimilar y z) :
    LinesRel lineSimilar x z := by
  induction hxy generalizing z with
  | nil => cases hyz; exact .nil
  | cons hxy _ ih =>
    cases hyz with
    | cons hyz htail => exact .cons (lineSimilar_trans _ _ _ ⟨hxy, hyz⟩) (ih htail)

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_sym"
  (words_as_type_indexed_bitvec)]
theorem codeSimilar_sym {width : Nat} [NeZero width] (left right : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    codeSimilar left right → codeSimilar right left := by
  induction left generalizing right with
  | nil => cases right <;> simp [codeSimilar]
  | cons sec rest ih =>
    cases right with
    | nil => simp [codeSimilar]
    | cons sec' rest' =>
      intro h
      exact ⟨ih rest' h.1, similarLines_sym h.2.1, h.2.2.symm⟩

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_trans"
  (words_as_type_indexed_bitvec)]
theorem codeSimilar_trans {width : Nat} [NeZero width] (x y z : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    codeSimilar x y ∧ codeSimilar y z → codeSimilar x z := by
  induction x generalizing y z with
  | nil =>
    cases y <;> cases z <;> simp [codeSimilar]
  | cons sec rest ih =>
    cases y with
    | nil => simp [codeSimilar]
    | cons sec' rest' =>
      cases z with
      | nil => simp [codeSimilar]
      | cons sec'' rest'' =>
        intro h
        exact ⟨ih rest' rest'' ⟨h.1.1, h.2.1⟩,
          similarLines_trans h.1.2.1 h.2.2.1, h.1.2.2.trans h.2.2.2⟩

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_append"
  (words_as_type_indexed_bitvec)]
theorem codeSimilar_append {width : Nat} [NeZero width] (l1 l2 r1 r2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    codeSimilar l1 l2 ∧ codeSimilar r1 r2 → codeSimilar (l1 ++ r1) (l2 ++ r2) := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => exact fun h => h.2
    | cons sec rest => simp [codeSimilar]
  | cons sec rest ih =>
    cases l2 with
    | nil => simp [codeSimilar]
    | cons sec' rest' =>
      intro h
      exact ⟨ih rest' ⟨h.1.1, h.2⟩, h.1.2⟩

/-- HOL's local overload at source line 49: LENGTH (FILTER (not o is_Label)).
The list and fixed byte carriers are retained; only the word dimension changes. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "len_no_lab"
  (words_as_type_indexed_bitvec)]
def lenNoLab {width : Nat} [NeZero width] (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Nat :=
  (lines.filter (fun line => !LabSem.isLabelHOL line)).length

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_sec_label_ok"
  (words_as_type_indexed_bitvec)]
theorem lineSimilar_secLabelOk {width : Nat} [NeZero width] (s : Nat) (l1 l2 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ line ∈ l1, secLabelOk s line) ∧ LinesRel lineSimilar l1 l2 →
      ∀ line ∈ l2, secLabelOk s line := by
  intro h
  rcases h with ⟨hok, hrel⟩
  induction hrel with
  | nil => simp
  | @cons x y xs ys hxy htail ih =>
    have hx := hok x (by simp)
    have hys := ih (fun line hmem => hok line (by simp [hmem]))
    intro line hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · cases x <;> cases line <;> simp only [lineSimilar] at hxy <;> try contradiction
      all_goals simp only [secLabelOk] at hx ⊢
      all_goals first | trivial | exact ⟨hxy.1.symm.trans hx.1, hxy.2 ▸ hx.2⟩
    · exact hys line hmem

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_sec_labels_ok"
  (words_as_type_indexed_bitvec)]
theorem codeSimilar_secLabelsOk {width : Nat} [NeZero width] (c1 c2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ c1, secLabelsOk sec) ∧ codeSimilar c1 c2 →
      ∀ sec ∈ c2, secLabelsOk sec := by
  induction c1 generalizing c2 with
  | nil => cases c2 <;> simp [codeSimilar]
  | cons sec rest ih =>
    cases c2 with
    | nil => simp
    | cons sec' rest' =>
      intro h target hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · have hok := h.1 sec (by simp)
        unfold secLabelsOk at hok ⊢
        rw [← h.2.2.2]
        exact lineSimilar_secLabelOk _ _ _ ⟨hok, h.2.2.1⟩
      · exact ih rest' ⟨fun sec hmem => h.1 sec (by simp [hmem]), h.2.1⟩ target hmem

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_similar_len_no_lab"
  (words_as_type_indexed_bitvec)]
theorem lineSimilar_lenNoLab {width : Nat} [NeZero width] (l1 l2 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    LinesRel lineSimilar l1 l2 → lenNoLab l1 = lenNoLab l2 := by
  intro h
  induction h with
  | nil => rfl
  | @cons x y xs ys hxy htail ih =>
    cases x <;> cases y <;> simp only [lineSimilar] at hxy <;> try contradiction
    all_goals simpa [lenNoLab, LabSem.isLabelHOL] using ih

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_len_no_lab"
  (words_as_type_indexed_bitvec)]
theorem codeSimilar_lenNoLab {width : Nat} [NeZero width] (c1 c2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    codeSimilar c1 c2 →
      c1.map (fun sec => lenNoLab sec.lines) = c2.map (fun sec => lenNoLab sec.lines) := by
  induction c1 generalizing c2 with
  | nil => cases c2 <;> simp [codeSimilar]
  | cons sec rest ih =>
    cases c2 with
    | nil => simp [codeSimilar]
    | cons sec' rest' =>
      intro h
      simp only [List.map_cons]
      rw [lineSimilar_lenNoLab _ _ h.2.1, ih rest' h.1]

end Flapjack.Compiler.Backend.LabToTarget
