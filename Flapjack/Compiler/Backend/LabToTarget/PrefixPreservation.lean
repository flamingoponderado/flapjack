import Flapjack.Compiler.Backend.LabToTarget.PrefixZero
import Flapjack.Compiler.Backend.LabToTarget.UpdatePosition
import Flapjack.Compiler.Backend.LabToTarget.SimpleEncoder
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Flapjack-specific finite-list logical complement; no EL operation involved. -/
private theorem nonlabelOfNotEvery {width : Nat} [NeZero width]
    (acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (hn : ¬∀ line ∈ acc, isLabelHOL line = true) :
    ∃ line ∈ acc.reverse, isLabelHOL line ≠ true := by
  classical
  by_cases h : ∃ line ∈ acc.reverse, isLabelHOL line ≠ true
  · exact h
  · apply False.elim
    apply hn
    intro line hm
    by_cases hy : isLabelHOL line = true
    · exact hy
    · exact False.elim (h ⟨line,by simpa using hm,hy⟩)

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_upd_lab_len_label_prefix_zero"
  (words_as_type_indexed_bitvec)]
theorem linesUpdLabLen_labelPrefixZero {width : Nat} [NeZero width]
    (pos : Nat) (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    ((∀ line ∈ acc, isLabelHOL line = true) → pos % 2 = 0) ∧ labelPrefixZero acc.reverse →
    labelPrefixZero (linesUpdLabLen pos ls acc).1 := by
  rintro ⟨hp,ha⟩
  induction ls generalizing pos acc with
  | nil => simpa [linesUpdLabLen] using ha
  | cons x xs ih =>
    cases x with
    | label k1 k2 len =>
      simp only [linesUpdLabLen]
      apply ih
      · intro _
        split <;> omega
      · simp only [List.reverse_cons]
        by_cases hall : ∀ line ∈ acc, isLabelHOL line = true
        · have he := hp hall
          apply labelPrefixZero_append
          exact ⟨ha,by simp [he,isLabelHOL,lineLen]⟩
        · exact labelPrefixZero_append_nonlabel _ _ ⟨ha,nonlabelOfNotEvery acc hall⟩
    | asm a bs len =>
      simp only [linesUpdLabLen]
      apply ih
      · intro h
        have hh := h (.asm a bs len) (by simp)
        simp [isLabelHOL] at hh
      · simp only [List.reverse_cons]
        apply labelPrefixZero_append
        exact ⟨ha,by simp [isLabelHOL]⟩
    | labAsm a w bs len =>
      simp only [linesUpdLabLen]
      apply ih
      · intro h
        have hh := h (.labAsm a w bs len) (by simp)
        simp [isLabelHOL] at hh
      · simp only [List.reverse_cons]
        apply labelPrefixZero_append
        exact ⟨ha,by simp [isLabelHOL]⟩

/-- Flapjack-specific equivalence of guarded optional-last and reverse-head predicates. -/
private theorem ends_iff {width : Nat} [NeZero width]
    (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    secEndsWithLabelNative sec ↔ sec.lines ≠ [] ∧ lastLabel sec.lines = true := by
  unfold secEndsWithLabelNative lastLabel
  rw [List.getLast?_eq_head?_reverse]
  have hn : sec.lines ≠ [] ↔ sec.lines.reverse ≠ [] := by simp
  rw [hn]
  cases sec.lines.reverse <;> simp

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "upd_lab_len_label_prefix_zero"
  (words_as_type_indexed_bitvec)]
theorem updLabLen_labelPrefixZero {width : Nat} [NeZero width]
    (pos : Nat) (ss : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    pos % 2 = 0 ∧ (∀ sec ∈ ss, secEndsWithLabelNative sec) →
    ∀ sec ∈ updLabLen pos ss, secLabelPrefixZero sec := by
  rintro ⟨hp,hends⟩
  induction ss generalizing pos with
  | nil => simp [updLabLen]
  | cons sec rest ih =>
    rcases sec with ⟨id,ls⟩
    have hl := linesUpdLabLen_labelPrefixZero pos ls [] ⟨fun _ => hp,by simp⟩
    have hend := (ends_iff ⟨id,ls⟩).mp (hends ⟨id,ls⟩ (by simp))
    have hout := linesUpdLabLen_evenLength pos ls [] (by simp [hend.1,hend.2,hp])
    have hpos := linesUpdLabLen_position pos ls []
    simp only [List.map_nil,List.sum_nil,Nat.sub_zero] at hpos
    have hp' : (linesUpdLabLen pos ls []).2 % 2 = 0 := by omega
    have hr := ih (linesUpdLabLen pos ls []).2 hp' (fun s hm => hends s (by simp [hm]))
    simpa [updLabLen,secLabelPrefixZero] using And.intro hl hr

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_label_prefix_zero"
  (words_as_type_indexed_bitvec)]
theorem encLinesAgainSimp_labelPrefixZero {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8)) (ls res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool) :
    encLinesAgainSimp labs ffis pos enc ls = (res,ok) ∧ labelPrefixZero ls → labelPrefixZero res := by
  induction ls generalizing pos res ok with
  | nil => rintro ⟨heq,_⟩; simp only [encLinesAgainSimp,Prod.mk.injEq] at heq; rcases heq with ⟨heq,_⟩; subst res; simp
  | cons line tail ih =>
    rintro ⟨heq,hls⟩
    cases line <;> simp only [encLinesAgainSimp] at heq
    all_goals try split at heq
    all_goals
      generalize hr : encLinesAgainSimp labs ffis _ enc tail = result at heq
      rcases result with ⟨rest,flag⟩
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨hres,hflag⟩
      subst res
      simp only [labelPrefixZero_cons_iff,isLabelHOL,lineLen,true_implies] at hls
      try have ht := ih _ rest flag ⟨hr,hls.2⟩
      simp_all [isLabelHOL,lineLen]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_label_prefix_zero"
  (words_as_type_indexed_bitvec)]
theorem encSecsAgain_labelPrefixZero {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (lines res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    encSecsAgain pos labs ffis enc lines = (res,ok) ∧
      (∀ sec ∈ lines, secLabelPrefixZero sec) →
    ∀ sec ∈ res, secLabelPrefixZero sec := by
  induction lines generalizing pos res ok with
  | nil => rintro ⟨heq,_⟩; simp only [encSecsAgain,Prod.mk.injEq] at heq; rcases heq with ⟨heq,_⟩; subst res; simp
  | cons sec tail ih =>
    rcases sec with ⟨id,ls⟩
    rintro ⟨heq,hls⟩
    simp only [encSecsAgain] at heq
    rw [encLinesAgainSimp_eq] at heq
    generalize hl : encLinesAgainSimp labs ffis pos enc ls = lr at heq
    rcases lr with ⟨ls',flag⟩
    simp only [List.reverse_nil,List.nil_append,Bool.true_and] at heq
    generalize hr : encSecsAgain (secLength ls' pos) labs ffis enc tail = rr at heq
    rcases rr with ⟨rest,flag'⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨hres,hflag⟩
    subst res
    have hfirst := encLinesAgainSimp_labelPrefixZero labs ffis pos enc ls ls' flag
      ⟨hl,hls ⟨id,ls⟩ (by simp)⟩
    have htail := ih _ rest flag' ⟨hr,fun sec hm => hls sec (by simp [hm])⟩
    simpa [secLabelPrefixZero] using And.intro hfirst htail

end Flapjack.Compiler.Backend.LabToTarget
