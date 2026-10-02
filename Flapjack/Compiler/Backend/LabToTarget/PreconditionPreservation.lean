import Flapjack.Compiler.Backend.LabSem.State
import Flapjack.Compiler.Backend.LabToTarget.SecondPass
import Flapjack.Compiler.Backend.LabToTarget.Padding
import Flapjack.Compiler.Backend.LabProps.Native

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabSem

/-- Flapjack induction infrastructure for the actual encoder projection. No
independently named HOL declaration; the full result equality is retained below. -/
private theorem encLines_pre {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8)) (lines acc : List (LabLineHOL width))
    (ok : Bool) (c : AsmConfigExact width)
    (hl : ∀ l ∈ lines,lineOkPreHOL c l) (ha : ∀ l ∈ acc,lineOkPreHOL c l) :
    ∀ l ∈ (encLinesAgain labs ffis pos enc lines acc ok).1,lineOkPreHOL c l := by
  induction lines generalizing pos acc ok with
  | nil => simpa [encLinesAgain] using ha
  | cons line tail ih =>
    have hhead := hl line (by simp)
    have ht : ∀ l ∈ tail,lineOkPreHOL c l := fun l hm => hl l (by simp [hm])
    cases line with
    | label k1 k2 len =>
      simp only [encLinesAgain]
      apply ih _ _ _ ht
      simpa [lineOkPreHOL] using ha
    | asm a bytes len =>
      simp only [encLinesAgain]
      apply ih _ _ _ ht
      simpa only [List.mem_cons,forall_eq_or_imp] using And.intro hhead ha
    | labAsm a w bytes len =>
      simp only [encLinesAgain]
      split
      · apply ih _ _ _ ht
        simpa [lineOkPreHOL] using ha
      · apply ih _ _ _ ht
        simpa [lineOkPreHOL] using ha

/-- Full original result equality and both EVERY guards; the returned pair is
Nat × Bool, not a successful-encoding assumption. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "enc_lines_again_all_enc_ok_pre" (words_as_type_indexed_bitvec)]
theorem encLinesAgain_pre {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8)) (lines acc : List (LabLineHOL width))
    (ok : Bool) (res : List (LabLineHOL width)) (result : Nat × Bool)
    (c : AsmConfigExact width) :
    encLinesAgain labs ffis pos enc lines acc ok = (res,result) ∧
    (∀ l ∈ lines,lineOkPreHOL c l) ∧ (∀ l ∈ acc,lineOkPreHOL c l) →
    ∀ l ∈ res,lineOkPreHOL c l := by
  rintro ⟨he,hl,ha⟩
  simpa only [he] using encLines_pre labs ffis pos enc lines acc ok c hl ha

/-- Full original section encoder theorem; returned flag remains arbitrary. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "enc_secs_again_all_enc_ok_pre" (words_as_type_indexed_bitvec)]
theorem encSecsAgain_pre {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (code res : List (Section (LabLineHOL width))) (ok : Bool) (c : AsmConfigExact width) :
    encSecsAgain pos labs ffis enc code = (res,ok) ∧ allEncOkPreHOL c code →
    allEncOkPreHOL c res := by
  have h : allEncOkPreHOL c code → allEncOkPreHOL c (encSecsAgain pos labs ffis enc code).1 := by
    induction code generalizing pos with
    | nil => simp [encSecsAgain,allEncOkPreHOL]
    | cons sec rest ih =>
      rcases sec with ⟨k,lines⟩
      intro hp
      have hl := hp ⟨k,lines⟩ (by simp)
      have hr : allEncOkPreHOL c rest := fun sec hm => hp sec (by simp [hm])
      simp only [encSecsAgain]
      intro sec hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact encLines_pre labs ffis pos enc lines [] true c hl (by simp)
      · exact ih _ hr sec hm
  rintro ⟨he,hp⟩
  simpa only [he] using h hp

/-- Full original add-NOP precondition preservation. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "line_ok_pre_add_nop" (words_as_type_indexed_bitvec)]
theorem addNop_pre {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (nop : List (BitVec 8)) (xs : List (LabLineHOL width)) :
    (∀ l ∈ xs,lineOkPreHOL c l) → ∀ l ∈ addNop nop xs,lineOkPreHOL c l := by
  induction xs with
  | nil => simp [addNop]
  | cons line tail ih =>
    intro hp
    have ht : ∀ l ∈ tail,lineOkPreHOL c l := fun l hm => hp l (by simp [hm])
    have hh := hp line (by simp)
    cases line with
    | label _ _ _ => simpa [addNop,lineOkPreHOL] using ih ht
    | asm _ _ _ => simpa [addNop,lineOkPreHOL] using And.intro hh ht
    | labAsm _ _ _ _ => simpa [addNop,lineOkPreHOL] using ht

/-- Full original padding theorem, including the accumulator guard. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "line_ok_pre_pad_section" (words_as_type_indexed_bitvec)]
theorem padSection_pre {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (xs acc : List (LabLineHOL width)) (c : AsmConfigExact width) :
    (∀ l ∈ xs,lineOkPreHOL c l) ∧ (∀ l ∈ acc,lineOkPreHOL c l) →
    ∀ l ∈ padSection nop xs acc,lineOkPreHOL c l := by
  induction xs generalizing acc with
  | nil => simp [padSection]
  | cons line tail ih =>
    rintro ⟨hp,ha⟩
    have ht : ∀ l ∈ tail,lineOkPreHOL c l := fun l hm => hp l (by simp [hm])
    have hh := hp line (by simp)
    cases line with
    | label k1 k2 len =>
      simp only [padSection]
      apply ih
      refine ⟨ht,?_⟩
      split
      · simpa [lineOkPreHOL] using ha
      · simpa [lineOkPreHOL] using addNop_pre c nop acc ha
    | asm a bytes len =>
      apply ih
      exact ⟨ht,by simpa [lineOkPreHOL] using And.intro hh ha⟩
    | labAsm a w bytes len =>
      apply ih
      exact ⟨ht,by simpa [lineOkPreHOL] using ha⟩

/-- Full original whole-code padding precondition theorem. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "all_enc_ok_pre_pad_code" (words_as_type_indexed_bitvec)]
theorem padCode_pre {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (code : List (Section (LabLineHOL width))) (c : AsmConfigExact width) :
    allEncOkPreHOL c code → allEncOkPreHOL c (padCode nop code) := by
  induction code with
  | nil => simp [padCode,allEncOkPreHOL]
  | cons sec rest ih =>
    rcases sec with ⟨k,lines⟩
    intro hp
    have hr : allEncOkPreHOL c rest := fun sec hm => hp sec (by simp [hm])
    simp only [padCode]
    intro sec hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact padSection_pre nop lines [] c ⟨hp ⟨k,lines⟩ (by simp),by simp⟩
    · exact ih hr sec hm

/-- Full original label-length update theorem, preserving both input lists. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "all_enc_ok_pre_lines_upd_lab_len" (words_as_type_indexed_bitvec)]
theorem linesUpdLabLen_pre {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (n : Nat) (lines acc : List (LabLineHOL width)) :
    (∀ l ∈ lines,lineOkPreHOL c l) ∧ (∀ l ∈ acc,lineOkPreHOL c l) →
    ∀ l ∈ (linesUpdLabLen n lines acc).1,lineOkPreHOL c l := by
  induction lines generalizing n acc with
  | nil => simp [linesUpdLabLen]
  | cons line tail ih =>
    rintro ⟨hp,ha⟩
    have ht : ∀ l ∈ tail,lineOkPreHOL c l := fun l hm => hp l (by simp [hm])
    have hh := hp line (by simp)
    cases line with
    | label k1 k2 len =>
      apply ih
      exact ⟨ht,by simpa [lineOkPreHOL] using ha⟩
    | asm a bytes len =>
      apply ih
      exact ⟨ht,by simpa [lineOkPreHOL] using And.intro hh ha⟩
    | labAsm a w bytes len =>
      apply ih
      exact ⟨ht,by simpa [lineOkPreHOL] using ha⟩

/-- Full original whole-code label-length update precondition theorem. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "all_enc_ok_pre_upd_lab_len" (words_as_type_indexed_bitvec)]
theorem updLabLen_pre {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (n : Nat) (code : List (Section (LabLineHOL width))) :
    allEncOkPreHOL c code → allEncOkPreHOL c (updLabLen n code) := by
  induction code generalizing n with
  | nil => simp [updLabLen,allEncOkPreHOL]
  | cons sec rest ih =>
    rcases sec with ⟨k,lines⟩
    intro hp
    have hr : allEncOkPreHOL c rest := fun sec hm => hp sec (by simp [hm])
    simp only [updLabLen]
    intro sec hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact linesUpdLabLen_pre c n lines [] ⟨hp ⟨k,lines⟩ (by simp),by simp⟩
    · exact ih _ hr sec hm
end Flapjack.Compiler.Backend.LabToTarget
