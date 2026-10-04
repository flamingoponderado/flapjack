import Flapjack.Compiler.Backend.LabToTarget.PositionValues

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def labelZero {width : Nat} [NeZero width]
    (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : Prop :=
  match line with
  | .label _ _ n => n = 0
  | _ => True

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def secLabelZero {width : Nat} [NeZero width]
    (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Prop :=
  ∀ line ∈ sec.lines, labelZero line

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem secLabelZero_posVal_zero {width : Nat} [NeZero width]
    (xs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (pos : Nat) :
    (∀ sec ∈ xs, secLabelZero sec) → posVal 0 pos xs = pos := by
  induction xs generalizing pos with
  | nil => simp [posVal]
  | cons sec xs ih =>
    rcases sec with ⟨k, lines⟩
    intro h
    have htail : ∀ sec ∈ xs, secLabelZero sec := fun sec hm => h sec (by simp [hm])
    have hlines : ∀ line ∈ lines, labelZero line := h ⟨k, lines⟩ (by simp)
    clear h
    induction lines generalizing pos with
    | nil => rw [posVal]; exact ih pos htail
    | cons line lines ihLines =>
      have hhead := hlines line (by simp)
      have ht : ∀ line ∈ lines, labelZero line := fun line hm => hlines line (by simp [hm])
      cases line with
      | label sid lid n =>
        simp only [labelZero] at hhead
        rw [posVal]
        simp only [isLabelHOL, ↓reduceIte, lineLength, hhead, Nat.add_zero]
        exact ihLines pos ht
      | asm _ _ _ => simp [posVal, isLabelHOL]
      | labAsm _ _ _ _ => simp [posVal, isLabelHOL]

/-- Full original append theorem, including the boundary equality branch and
physical-byte shift, with zero label annotations required only of the suffix. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem posVal_append {width : Nat} [NeZero width]
    (c1 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (i pos : Nat)
    (c2 : List (Section (LabLineHOL width))) :
    (∀ sec ∈ c2, secLabelZero sec) →
    posVal i pos (c1 ++ c2) =
      if i ≤ (c1.map (fun sec => lenNoLab sec.lines)).sum then posVal i pos c1
      else posVal (i - (c1.map (fun sec => lenNoLab sec.lines)).sum)
        (pos + (c1.map (fun sec => (sec.lines.map lineLength).sum)).sum) c2 := by
  intro hzero
  induction c1 generalizing i pos with
  | nil =>
    simp only [List.nil_append, List.map_nil, List.sum_nil, Nat.sub_zero, Nat.add_zero]
    by_cases hi : i ≤ 0
    · have hz : i = 0 := by omega
      subst i
      simp only [Nat.le_refl, ↓reduceIte]
      rw [posVal]
      exact secLabelZero_posVal_zero c2 pos hzero
    · simp [hi]
  | cons sec c1 ih =>
    rcases sec with ⟨k, lines⟩
    simp only [List.cons_append, List.map_cons, List.sum_cons]
    rw [posVal_decompose]
    cases hr : secPosVal i pos lines with
    | some x =>
      have hi : i ≤ lenNoLab lines + (c1.map (fun sec => lenNoLab sec.lines)).sum := by
        by_cases hn : i ≤ lenNoLab lines + (c1.map (fun sec => lenNoLab sec.lines)).sum
        · exact hn
        · have hex := secPosVal_tooBig i pos lines (by omega)
          simp [hr] at hex
      simp only [hr, if_pos hi]
      rw [posVal_decompose]
      simp [hr]
    | none =>
      simp only [hr]
      rw [ih]
      by_cases hi : i ≤ lenNoLab lines + (c1.map (fun sec => lenNoLab sec.lines)).sum
      · have hrem : i - lenNoLab lines ≤ (c1.map (fun sec => lenNoLab sec.lines)).sum := by omega
        simp only [if_pos hi, if_pos hrem]
        rw [posVal_decompose i pos (⟨k, lines⟩ :: c1)]
        simp [hr]
      · have hrem : ¬ i - lenNoLab lines ≤ (c1.map (fun sec => lenNoLab sec.lines)).sum := by omega
        simp only [if_neg hi, if_neg hrem]
        simp [Nat.sub_sub, Nat.add_assoc]

end Flapjack.Compiler.Backend.LabToTarget
