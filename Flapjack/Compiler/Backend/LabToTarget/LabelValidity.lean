import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Encoding
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Padding

/-! Full original section-label validity chain through initial encoding,
repeated encoding, label-length updates and padding. Accumulators retain all
original validity premises; none of the returned validity facts are assumed. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabProps

/-- Reflexive list-relation infrastructure, without a separate HOL original. -/
private theorem selfRelated {width : Nat} [NeZero width]
    (xs : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : LinesRel lineSimilar xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (lineSimilar_refl x) ih

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_sec_list_sec_labels_ok"
  (words_as_type_indexed_bitvec)]
theorem encSecList_secLabelsOk {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ code, secLabelsOk sec) →
      ∀ sec ∈ encSecList enc code, secLabelsOk sec := by
  intro h
  apply codeSimilar_secLabelsOk code (encSecList enc code)
  exact ⟨h, codeSimilar_sym _ _ ((codeSimilar_encSecList code code enc).mpr
    (codeSimilar_refl code))⟩

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_sec_labels_ok"
  (words_as_type_indexed_bitvec)]
theorem encLinesAgain_secLabelOk {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (lines acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool)
    (res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok' : Nat × Bool) (k : Nat) :
    encLinesAgain labs ffis pos enc lines acc ok = (res,ok') ∧
      (∀ line ∈ acc, secLabelOk k line) ∧
      (∀ line ∈ lines, secLabelOk k line) →
    ∀ line ∈ res, secLabelOk k line := by
  intro h
  apply lineSimilar_secLabelOk k (acc.reverse ++ lines) res
  refine ⟨?_, encLinesAgain_implies_similar labs ffis pos enc lines acc ok
    res ok' acc.reverse h.1 (selfRelated _)⟩
  intro line hm
  simp only [List.mem_append, List.mem_reverse] at hm
  exact hm.elim (h.2.1 line) (h.2.2 line)

/-- Source's unused k:beta is vacuous and omitted after full type review.
The source binder named ffis actually carries the label map, and labs the FFI
names; the argument positions and full operation are retained. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_sec_labels_ok"
  (words_as_type_indexed_bitvec)]
theorem encSecsAgain_secLabelsOk {width : Nat} [NeZero width]
    (pos : Nat) (labels : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (ls res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    encSecsAgain pos labels ffis enc ls = (res,ok) ∧
      (∀ sec ∈ ls, secLabelsOk sec) →
    ∀ sec ∈ res, secLabelsOk sec := by
  intro h
  exact codeSimilar_secLabelsOk ls res
    ⟨h.2, encSecsAgain_implies_similar pos labels ffis enc ls res ok h.1⟩

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_upd_lab_len_sec_label_ok"
  (words_as_type_indexed_bitvec)]
theorem linesUpdLabLen_secLabelOk {width : Nat} [NeZero width]
    (pos : Nat) (lines acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (k : Nat) :
    (∀ line ∈ lines, secLabelOk k line) ∧
      (∀ line ∈ acc, secLabelOk k line) →
    ∀ line ∈ (linesUpdLabLen pos lines acc).1, secLabelOk k line := by
  fun_induction linesUpdLabLen pos lines acc <;>
    simp_all [secLabelOk]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "upd_lab_len_sec_labels_ok"
  (words_as_type_indexed_bitvec)]
theorem updLabLen_secLabelsOk {width : Nat} [NeZero width]
    (n : Nat) (ls : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ ls, secLabelsOk sec) →
      ∀ sec ∈ updLabLen n ls, secLabelsOk sec := by
  induction ls generalizing n with
  | nil => simp [updLabLen]
  | cons sec rest ih =>
    rcases sec with ⟨id,lines⟩
    intro h
    have hs := h ⟨id,lines⟩ (by simp)
    have hr := ih (linesUpdLabLen n lines []).2
      (fun s hm => h s (by simp [hm]))
    have hl := linesUpdLabLen_secLabelOk n lines [] id
      ⟨hs, by simp⟩
    simpa [updLabLen, secLabelsOk] using And.intro hl hr

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "add_nop_sec_label_ok"
  (words_as_type_indexed_bitvec)]
theorem addNop_secLabelOk {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (k : Nat) :
    (∀ line ∈ aux, secLabelOk k line) →
      ∀ line ∈ addNop nop aux, secLabelOk k line := by
  intro h
  exact lineSimilar_secLabelOk k aux (addNop nop aux)
    ⟨h, lineSimilar_addNop aux aux nop (selfRelated _)⟩

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pad_section_sec_label_ok"
  (words_as_type_indexed_bitvec)]
theorem padSection_secLabelOk {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (xs acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (k : Nat) :
    (∀ line ∈ xs, secLabelOk k line) ∧
      (∀ line ∈ acc, secLabelOk k line) →
    ∀ line ∈ padSection nop xs acc, secLabelOk k line := by
  intro h
  apply lineSimilar_secLabelOk k (acc.reverse ++ xs) (padSection nop xs acc)
  refine ⟨?_, lineSimilar_padSection nop xs acc (acc.reverse ++ xs) (selfRelated _)⟩
  intro line hm
  simp only [List.mem_append, List.mem_reverse] at hm
  exact hm.elim (h.2 line) (h.1 line)

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pad_code_sec_labels_ok"
  (words_as_type_indexed_bitvec)]
theorem padCode_secLabelsOk {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ code, secLabelsOk sec) →
      ∀ sec ∈ padCode nop code, secLabelsOk sec := by
  intro h
  exact codeSimilar_secLabelsOk code (padCode nop code)
    ⟨h, codeSimilar_padCode code code nop (codeSimilar_refl code)⟩

end Flapjack.Compiler.Backend.LabToTarget
