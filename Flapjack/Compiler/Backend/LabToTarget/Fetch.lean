import Flapjack.Compiler.Backend.LabSem.Navigation

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabSem

/-- Structural termination measure only, with no independent HOL original. -/
private def fetchSize {width : Nat} [NeZero width] (code : LabProgHOL width) : Nat :=
  (code.map (fun sec => sec.lines.length + 1)).sum

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def numPcs {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Nat :=
  match code with
  | [] => 0
  | ⟨_, []⟩ :: rest => numPcs rest
  | ⟨sectionId, line :: lines⟩ :: rest =>
      if isLabelHOL line then numPcs (⟨sectionId, lines⟩ :: rest)
      else 1 + numPcs (⟨sectionId, lines⟩ :: rest)
termination_by fetchSize code
decreasing_by all_goals simp_wf; simp_all [fetchSize] <;> omega

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem asmFetchAux_append1 {width : Nat} [NeZero width]
    (pc : Nat) (code secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    pc < numPcs code → asmFetchAux pc (code ++ secList) = asmFetchAux pc code := by
  induction code generalizing pc with
  | nil => simp [numPcs]
  | cons sec rest ih =>
    rcases sec with ⟨sectionId, lines⟩
    induction lines generalizing pc with
    | nil => simpa [numPcs, asmFetchAux] using ih pc
    | cons line lines ihLines =>
      cases line with
      | label s l len => simpa [numPcs, asmFetchAux, isLabelHOL] using ihLines pc
      | asm a bytes len =>
        cases pc with
        | zero => simp [asmFetchAux, isLabelHOL]
        | succ pc =>
          intro h
          have hpc : pc < numPcs (⟨sectionId, lines⟩ :: rest) := by
            simp only [numPcs, isLabelHOL, Bool.false_eq_true, ↓reduceIte] at h
            omega
          simpa [asmFetchAux, isLabelHOL] using ihLines pc hpc
      | labAsm a w bytes len =>
        cases pc with
        | zero => simp [asmFetchAux, isLabelHOL]
        | succ pc =>
          intro h
          have hpc : pc < numPcs (⟨sectionId, lines⟩ :: rest) := by
            simp only [numPcs, isLabelHOL, Bool.false_eq_true, ↓reduceIte] at h
            omega
          simpa [asmFetchAux, isLabelHOL] using ihLines pc hpc

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem asmFetchAux_append2 {width : Nat} [NeZero width]
    (pc : Nat) (code secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    asmFetchAux (pc + numPcs code) (code ++ secList) = asmFetchAux pc secList := by
  induction code with
  | nil => simp [numPcs]
  | cons sec rest ih =>
    rcases sec with ⟨sectionId, lines⟩
    induction lines with
    | nil => simpa [numPcs, asmFetchAux] using ih
    | cons line lines ihLines =>
      have advance (n : Nat) : pc + (1 + n) - 1 = pc + n := by omega
      cases line <;>
        simpa [numPcs, asmFetchAux, isLabelHOL, advance] using ihLines

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem asmFetchAux_mem {width : Nat} [NeZero width] (n : Nat)
    (x : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    x ∈ lines ∧ isLabelHOL x = false →
      ∃ pc, asmFetchAux pc [⟨n, lines⟩] = some x := by
  induction lines with
  | nil => simp
  | cons line lines ih =>
    intro h
    rcases List.mem_cons.mp h.1 with heq | hmem
    · subst x
      cases line with
      | label s l len => simp [isLabelHOL] at h
      | asm a bytes len => exact ⟨0, by simp [asmFetchAux, isLabelHOL]⟩
      | labAsm a w bytes len => exact ⟨0, by simp [asmFetchAux, isLabelHOL]⟩
    · obtain ⟨pc, hpc⟩ := ih ⟨hmem, h.2⟩
      cases line with
      | label s l len => exact ⟨pc, by simpa [asmFetchAux, isLabelHOL] using hpc⟩
      | asm a bytes len => exact ⟨pc + 1, by simpa [asmFetchAux, isLabelHOL] using hpc⟩
      | labAsm a w bytes len => exact ⟨pc + 1, by simpa [asmFetchAux, isLabelHOL] using hpc⟩

end Flapjack.Compiler.Backend.LabToTarget
