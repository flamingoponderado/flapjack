import Flapjack.Compiler.Backend.LabToTarget.EvenLabels
import Flapjack.Compiler.Backend.LabToTarget.LabelPosition
import Flapjack.Compiler.Backend.LabToTarget.PositionAppend
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Both original zero-label and position-validity guards are retained. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "label_zero_pos_ok_lines_even_labels" (words_as_type_indexed_bitvec)]
theorem labelZero_posOk_linesEvenLabels {width : Nat} [NeZero width] (pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ line ∈ lines, labelZero line) ∧ labLenPosOk pos lines → linesEvenLabels pos lines := by
  induction lines generalizing pos with
  | nil => simp [linesEvenLabels]
  | cons line rest ih =>
    rintro ⟨hz,hp⟩
    have hzero := hz line (by simp)
    have hrest : ∀ l ∈ rest,labelZero l := fun l hm => hz l (by simp [hm])
    rcases hp with ⟨hp,hpt⟩
    rw [linesEvenLabels]
    refine ⟨?_,ih _ ⟨hrest,hpt⟩⟩
    cases line with
    | label sid lid len =>
      simp only [labelZero] at hzero
      simp only [lineLabLenPosOk,hzero] at hp
      by_cases he : pos % 2 = 0
      · intro _; exact he
      · simp [he] at hp
    | asm _ _ _ => simp [isLabelHOL]
    | labAsm _ _ _ _ => simp [isLabelHOL]

/-- Full original section theorem with both guards and actual annotation advancement. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "label_zero_pos_ok_even_labels" (words_as_type_indexed_bitvec)]
theorem labelZero_posOk_evenLabels {width : Nat} [NeZero width] (pos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ code,secLabelZero sec) ∧ allLabLenPosOk pos code → evenLabels pos code := by
  induction code generalizing pos with
  | nil => simp [evenLabels]
  | cons sec rest ih =>
    rcases sec with ⟨k,lines⟩
    rintro ⟨hz,hp⟩
    have hzero := hz ⟨k,lines⟩ (by simp)
    have hrest : ∀ sec ∈ rest,secLabelZero sec := fun sec hm => hz sec (by simp [hm])
    rcases hp with ⟨hp,hpt⟩
    rw [(evenLabels_alt (emptyWidth := width) pos k lines rest).2]
    refine ⟨labelZero_posOk_linesEvenLabels pos lines ⟨hzero,hp⟩,?_⟩
    have ht := ih (pos + secLength lines 0) ⟨hrest,hpt⟩
    simpa [secLengthSumLineLen] using ht
end Flapjack.Compiler.Backend.LabToTarget
