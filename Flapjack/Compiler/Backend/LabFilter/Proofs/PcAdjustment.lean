import Flapjack.Compiler.Backend.LabFilter.Proofs.StateRelation

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

private theorem adjustPcZero {width : Nat} [NeZero width] (code : LabProgHOL width) :
    adjustPc 0 code = 0 := by rw [adjustPc.eq_def]; simp

/-- Flapjack one-position consequence of the literal PC-adjustment definition;
no separate original HOL declaration. -/
private theorem adjustPcSucc {width : Nat} [NeZero width] (pc : Nat)
    (code : LabProgHOL width) :
    (∀ bytes len, asmFetchAux pc code = some (.asm (.asmi (.inst .skip)) bytes len) →
      adjustPc (pc + 1) code = adjustPc pc code) ∧
    ((∀ bytes len, asmFetchAux pc code ≠ some (.asm (.asmi (.inst .skip)) bytes len)) →
      adjustPc (pc + 1) code = adjustPc pc code + 1) := by
  induction code generalizing pc with
  | nil => cases pc <;> simp [asmFetchAux, adjustPc]
  | cons sect rest ih =>
    rcases sect with ⟨k, lines⟩
    induction lines generalizing pc with
    | nil =>
      cases pc with
      | zero => simpa [asmFetchAux, adjustPc, adjustPcZero] using ih 0
      | succ pc => simpa [asmFetchAux, adjustPc, adjustPcZero] using ih (pc + 1)
    | cons line lines ih =>
      by_cases hl : isLabelHOL line = true
      · cases pc with
        | zero => simpa [asmFetchAux, adjustPc, hl, adjustPcZero] using ih 0
        | succ pc => simpa [asmFetchAux, adjustPc, hl, adjustPcZero] using ih (pc + 1)
      · cases pc with
        | zero =>
          cases line <;> simp_all [asmFetchAux, isLabelHOL, notSkip, adjustPc, adjustPcZero]
        | succ pc =>
          constructor
          · intro bytes len hf
            have he := (ih pc).1 bytes len (by simpa [asmFetchAux, hl] using hf)
            simp [adjustPc, hl, he]
          · intro hn
            have ht : ∀ bytes len, asmFetchAux pc (⟨k, lines⟩ :: rest) ≠
                some (.asm (.asmi (.inst .skip)) bytes len) := by
              simpa [asmFetchAux, hl] using hn
            have he := (ih pc).2 ht
            simp [adjustPc, hl, he, Nat.add_assoc]
            split <;> rfl

/-- Flapjack finite-run consequence of adjustPcSucc; no separate HOL original. -/
private theorem adjustPcSkippedPrefix {width : Nat} [NeZero width] (count pc : Nat)
    (code : LabProgHOL width)
    (h : ∀ i, i < count → ∃ bytes len,
      asmFetchAux (pc + i) code = some (.asm (.asmi (.inst .skip)) bytes len)) :
    adjustPc (pc + count) code = adjustPc pc code := by
  induction count generalizing pc with
  | zero => simp
  | succ count ih =>
    obtain ⟨bytes, len, hf⟩ := h 0 (Nat.succ_pos count)
    have he := (adjustPcSucc pc code).1 bytes len (by simpa only [Nat.add_zero] using hf)
    have ht : ∀ i, i < count → ∃ bytes len,
        asmFetchAux (pc + 1 + i) code = some (.asm (.asmi (.inst .skip)) bytes len) := by
      intro i hi
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (i + 1) (by omega)
    have hp := ih (pc + 1) ht
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.trans he

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem adjustPcAllSkips {width : Nat} [NeZero width] (count pc : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) :
    allSkips pc code count → adjustPc pc code + 1 = adjustPc (pc + count + 1) code := by
  intro h
  have he := (adjustPcSucc (pc + count) code).2 h.1
  rw [adjustPcSkippedPrefix count pc code h.2] at he
  exact he.symm

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allSkipsInitialAdjust {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) :
    ∃ count, allSkips 0 code count ∧ adjustPc count code = 0 := by
  obtain ⟨count, _, hs⟩ := asmFetchAuxEq 0 code
  refine ⟨count, hs, ?_⟩
  simpa only [Nat.zero_add, adjustPcZero] using adjustPcSkippedPrefix count 0 code hs.2

end Flapjack.Compiler.Backend.LabFilter.Proofs
