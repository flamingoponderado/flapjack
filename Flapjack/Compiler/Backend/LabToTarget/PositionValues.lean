import Flapjack.Compiler.Backend.LabProps.LineLength
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps

/-- Original section-local byte position: label lines consume physical bytes
without consuming an instruction index; exhaustion is NONE. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def secPosVal {width : Nat} [NeZero width] (i pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Option Nat :=
  match lines with
  | [] => none
  | y :: ys =>
    if isLabelHOL y then secPosVal i (pos + lineLength y) ys
    else if i = 0 then some pos
    else secPosVal (i - 1) (pos + lineLength y) ys

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem secPosVal_tooBig {width : Nat} [NeZero width] (i pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    lenNoLab lines ≤ i → secPosVal i pos lines = none := by
  induction lines generalizing i pos with
  | nil => simp [secPosVal]
  | cons y ys ih =>
    cases y <;> simp only [secPosVal, isLabelHOL, Bool.false_eq_true, ↓reduceIte]
    · intro h
      apply ih
      simpa [lenNoLab, isLabelHOL] using h
    all_goals
      intro h
      have hcount : lenNoLab ys + 1 ≤ i := by
        simpa [lenNoLab, isLabelHOL] using h
      have hn : i ≠ 0 := by omega
      simp only [hn, ↓reduceIte]
      apply ih
      omega

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem everyIsLabel_secPosVal {width : Nat} [NeZero width] (n pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ line ∈ lines, isLabelHOL line = true) → secPosVal n pos lines = none := by
  induction lines generalizing n pos with
  | nil => simp [secPosVal]
  | cons y ys ih =>
    intro h
    have hy := h y (by simp)
    simp only [secPosVal, hy, ↓reduceIte]
    exact ih n _ (fun line hl => h line (by simp [hl]))

/-- Original whole-code position recursion, retaining empty sections and label
physical lengths. The termination measure only justifies the source recursion. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def posVal {width : Nat} [NeZero width] (i pos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Nat :=
  match code with
  | [] => pos
  | ⟨_, []⟩ :: xs => posVal i pos xs
  | ⟨k, y :: ys⟩ :: xs =>
    if isLabelHOL y then posVal i (pos + lineLength y) (⟨k, ys⟩ :: xs)
    else if i = 0 then pos
    else posVal (i - 1) (pos + lineLength y) (⟨k, ys⟩ :: xs)
termination_by code.length + (code.map (fun sec => sec.lines.length)).sum
decreasing_by all_goals simp_wf <;> omega

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem posVal_decompose {width : Nat} [NeZero width] (i pos : Nat)
    (acc : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    posVal i pos acc = match acc with
      | [] => pos
      | ⟨_, s⟩ :: ss => match secPosVal i pos s with
        | none => posVal (i - lenNoLab s) (pos + (s.map lineLength).sum) ss
        | some x => x := by
  cases acc with
  | nil => rw [posVal]
  | cons sec ss =>
    rcases sec with ⟨k, s⟩
    induction s generalizing i pos with
    | nil => simp [posVal, secPosVal, lenNoLab]
    | cons y ys ih =>
      rw [posVal]
      cases y <;> simp only [secPosVal, isLabelHOL, Bool.false_eq_true,
        ↓reduceIte, lenNoLab, List.filter_cons, Bool.not_true, Bool.not_false,
        List.length_cons, List.map_cons, List.sum_cons]
      · rw [ih]
        simp [lenNoLab, isLabelHOL, Nat.add_assoc]
      all_goals
        by_cases hi : i = 0
        · simp [hi]
        · simp only [hi, ↓reduceIte]
          rw [ih]
          simp [lenNoLab, isLabelHOL, Nat.add_left_comm, Nat.sub_sub, Nat.add_comm]

/-- The original empty-code conjunct has its own polymorphic word index,
independent of the nonempty section's word index; both are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem posVal_sections {emptyWidth : Nat} {width : Nat} [NeZero emptyWidth] [NeZero width]
    (i pos k : Nat)
    (s : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (ss : List (Section (LabLineHOL width))) :
    posVal i pos ([] : List (Section (LabLineHOL emptyWidth))) = pos ∧
    posVal i pos (⟨k, s⟩ :: ss) = match secPosVal i pos s with
      | none => posVal (i - lenNoLab s) (pos + (s.map lineLength).sum) ss
      | some x => x := by
  constructor <;> exact posVal_decompose _ _ _

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem posVal_acc {width : Nat} [NeZero width]
    (ls : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (n : Nat) :
    posVal (ls.map (fun sec => lenNoLab sec.lines)).sum n ls =
      n + (ls.map (fun sec => (sec.lines.map lineLength).sum)).sum := by
  induction ls generalizing n with
  | nil => simp [posVal]
  | cons sec ls ih =>
    rcases sec with ⟨k, s⟩
    simp only [List.map_cons, List.sum_cons]
    rw [posVal_decompose]
    have hexhaust := secPosVal_tooBig
      (lenNoLab s + (ls.map (fun sec => lenNoLab sec.lines)).sum) n s
      (Nat.le_add_right _ _)
    simp only [hexhaust, Nat.add_sub_cancel_left]
    rw [ih]
    simp [Nat.add_assoc]

end Flapjack.Compiler.Backend.LabToTarget
