import Flapjack.Compiler.Backend.LabToTarget.SimpleEncoder
import Flapjack.Compiler.Backend.LabToTarget.SectionLength
import Flapjack.Compiler.Backend.LabToTarget.LabelLookup
import Flapjack.Compiler.Backend.LabSem.State

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original untouched-section lookup theorem; its sole guard is absence
of the queried outer key from the section-number list. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "lab_lookup_compute_labels_alt_ignore" (words_as_type_indexed_bitvec)]
theorem labLookup_computeLabelsAlt_ignore {width : Nat} [NeZero width]
    (pos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (acc : Spt (Spt Nat)) (n1 n2 : Nat) :
    n1 ∉ code.map (fun sec => sec.sectionId) →
    labLookup n1 n2 (computeLabelsAlt pos code acc) = labLookup n1 n2 acc := by
  induction code generalizing pos acc with
  | nil => simp [computeLabelsAlt]
  | cons sec rest ih =>
    intro hn
    have h : n1 ≠ sec.sectionId ∧ n1 ∉ rest.map (fun sec => sec.sectionId) := by
      simpa using hn
    generalize he : sectionLabels pos sec.lines [] = entry
    rcases entry with ⟨newPos,secLabs⟩
    simp only [computeLabelsAlt,he]
    rw [ih newPos _ h.2]
    simp only [labLookup,sptLookup_sptInsert_ne sec.sectionId n1 _ acc h.1]

/-- Full original complete section-label pair preservation, with precisely the
source true-flag result equality and the arbitrary association accumulator. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "enc_lines_again_section_labels" (words_as_type_indexed_bitvec)]
theorem encLinesAgain_sectionLabels {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (lines res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (acc : List (Nat × Nat)) :
    encLinesAgainSimp labs ffis pos enc lines = (res,true) →
    sectionLabels pos lines acc = sectionLabels pos res acc := by
  induction lines generalizing pos res acc with
  | nil =>
    intro he
    have hr : res = [] := (Prod.mk.inj he).1.symm
    subst res
    rfl
  | cons line tail ih =>
    intro he
    cases line <;> simp only [encLinesAgainSimp] at he
    all_goals try split at he
    all_goals
      generalize ht : encLinesAgainSimp labs ffis _ enc tail = result at he
      rcases result with ⟨rest,flag⟩
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨hres,hflag⟩
      subst res
    all_goals try
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hflag
      rcases hflag with ⟨hlen,hflag⟩
      simp only [hlen] at ht ⊢
    all_goals
      have hr : flag = true := hflag
      subst flag
      simp only [sectionLabels]
      first
      | split <;> exact ih _ rest _ ht
      | exact ih _ rest acc ht

/-- Full original equality of computed nested maps. Only the original successful
section-encoder result equality is assumed; no map freshness or validity guard. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "enc_secs_again_compute_labels" (words_as_type_indexed_bitvec)]
theorem encSecsAgain_computeLabels {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (code res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (acc : Spt (Spt Nat)) :
    encSecsAgain pos labs ffis enc code = (res,true) →
    computeLabelsAlt pos res acc = computeLabelsAlt pos code acc := by
  induction code generalizing pos res acc with
  | nil =>
    intro he
    have hr : res = [] := (Prod.mk.inj he).1.symm
    subst res
    rfl
  | cons sec rest ih =>
    rcases sec with ⟨k,lines⟩
    intro he
    simp only [encSecsAgain] at he
    rw [encLinesAgainSimp_eq labs ffis pos enc lines [] true] at he
    generalize hl : encLinesAgainSimp labs ffis pos enc lines = lr at he
    rcases lr with ⟨lines1,flag⟩
    simp only [List.reverse_nil,List.nil_append,Bool.true_and] at he
    generalize ht : encSecsAgain (secLength lines1 pos) labs ffis enc rest = tr at he
    rcases tr with ⟨rest1,flag1⟩
    simp only [Prod.mk.injEq,Bool.and_eq_true] at he
    rcases he with ⟨hres,hflag,hflag1⟩
    subst res
    subst flag
    subst flag1
    have hlabels := encLinesAgain_sectionLabels labs ffis pos enc lines lines1 [] hl
    simp only [computeLabelsAlt]
    rw [←hlabels]
    rw [←sectionLabelsSecLength pos lines1 []] at ht
    rw [←hlabels] at ht
    exact ih _ rest1 _ ht
end Flapjack.Compiler.Backend.LabToTarget
