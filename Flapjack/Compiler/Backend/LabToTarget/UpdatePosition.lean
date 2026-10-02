import Flapjack.Compiler.Backend.LabToTarget.SecondPass
import Flapjack.Compiler.Backend.LabToTarget.LineLength
import Flapjack.Compiler.Backend.LabToTarget.EndingLabels

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Flapjack-specific arithmetic conservation lemma for the original update. -/
private theorem updateConservation {width : Nat} [NeZero width]
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos : Nat) (acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (linesUpdLabLen pos lines acc).2 + (acc.map lineLen).sum =
    pos + ((linesUpdLabLen pos lines acc).1.map lineLen).sum := by
  induction lines generalizing pos acc with
  | nil => simp [linesUpdLabLen, List.map_reverse]
  | cons x xs ih =>
    cases x with
    | label k1 k2 l =>
      have h := ih (pos + (if pos % 2 = 0 then 0 else 1))
        (.label k1 k2 (if pos % 2 = 0 then 0 else 1) :: acc)
      simp only [List.map_cons, List.sum_cons, lineLen] at h
      simpa only [linesUpdLabLen] using (by omega :
        (linesUpdLabLen (pos + (if pos % 2 = 0 then 0 else 1)) xs
          (.label k1 k2 (if pos % 2 = 0 then 0 else 1) :: acc)).2 +
          (acc.map lineLen).sum = pos +
          ((linesUpdLabLen (pos + (if pos % 2 = 0 then 0 else 1)) xs
          (.label k1 k2 (if pos % 2 = 0 then 0 else 1) :: acc)).1.map lineLen).sum)
    | asm a bs l =>
      have h := ih (pos + l) (.asm a bs l :: acc)
      simp only [List.map_cons, List.sum_cons, lineLen] at h
      simp only [linesUpdLabLen]
      omega
    | labAsm a w bs l =>
      have h := ih (pos + l) (.labAsm a w bs l :: acc)
      simp only [List.map_cons, List.sum_cons, lineLen] at h
      simp only [linesUpdLabLen]
      omega

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "SND_lines_upd_lab_len"
  (words_as_type_indexed_bitvec)]
theorem linesUpdLabLen_position {width : Nat} [NeZero width]
    (pos : Nat) (lines acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (linesUpdLabLen pos lines acc).2 =
    pos + ((linesUpdLabLen pos lines acc).1.map lineLen).sum - (acc.map lineLen).sum := by
  have h := updateConservation lines pos acc
  omega

/-- Flapjack-specific final-position parity under the original guarded LAST premise. -/
private theorem finalPositionEven {width : Nat} [NeZero width]
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos : Nat) (acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (hne : lines ≠ []) (hlast : lastLabel lines = true) :
    (linesUpdLabLen pos lines acc).2 % 2 = 0 := by
  induction lines generalizing pos acc with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases x <;> simp_all [lastLabel, isLabelHOL, linesUpdLabLen]
      split <;> omega
    | cons y ys =>
      have hl : lastLabel (y :: ys) = true := by
        simpa only [lastLabel, List.getLast?_cons_of_ne_nil (by simp : y :: ys ≠ [])] using hlast
      cases x <;> simp only [linesUpdLabLen] <;> apply ih <;> simp_all

/-- The original conditional premise guards LAST by the nonempty branch;
`lastLabel` contributes no interpretation of total HOL LAST on an empty list. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "EVEN_sec_length_lines_upd_lab_len"
  (words_as_type_indexed_bitvec)]
theorem linesUpdLabLen_evenLength {width : Nat} [NeZero width]
    (pos : Nat) (lines acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (if lines = [] then pos % 2 = 0 ∧ (acc.map lineLen).sum % 2 = 0
      else lastLabel lines = true ∧ (pos + (acc.map lineLen).sum) % 2 = 0) →
    ((linesUpdLabLen pos lines acc).1.map lineLen).sum % 2 = 0 := by
  intro h
  by_cases hn : lines = []
  · subst lines
    simpa [linesUpdLabLen, List.map_reverse] using h.2
  · simp only [if_neg hn] at h
    have hf := finalPositionEven lines pos acc hn h.1
    have hc := updateConservation lines pos acc
    have hp := h.2
    omega

end Flapjack.Compiler.Backend.LabToTarget
