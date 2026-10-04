import Flapjack.Compiler.Backend.LabToTarget.FilterSkip
import Flapjack.Compiler.Backend.LabSem.Evaluate

/-! Original skip-filter PC adjustment and finite skipped-instruction runs.
These use the executed filter and the full native source fetch/evaluator.
-/
namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

private def codeSize {width : Nat} [NeZero width] (code : LabProgHOL width) : Nat :=
  (code.map (fun sect => sect.lines.length + 1)).sum

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def adjustPc {width : Nat} [NeZero width] (pc : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) : Nat :=
  if pc = 0 then 0 else
  match code with
  | [] => pc
  | ⟨_, []⟩ :: rest => adjustPc pc rest
  | ⟨k, line :: lines⟩ :: rest =>
      if isLabelHOL line then adjustPc pc (⟨k, lines⟩ :: rest)
      else if notSkip line then adjustPc (pc - 1) (⟨k, lines⟩ :: rest) + 1
      else adjustPc (pc - 1) (⟨k, lines⟩ :: rest)
termination_by codeSize code
decreasing_by all_goals simp_all [codeSize]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def allSkips {width : Nat} [NeZero width] (pc : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) (count : Nat) : Prop :=
  (∀ bytes len, asmFetchAux (pc + count) code ≠ some (.asm (.asmi (.inst .skip)) bytes len)) ∧
    ∀ i, i < count → ∃ bytes len,
      asmFetchAux (pc + i) code = some (.asm (.asmi (.inst .skip)) bytes len)

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem isLabelNotSkip {width : Nat} [NeZero width]
    (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)) : isLabelHOL line = true → notSkip line = true := by
  cases line <;> simp [isLabelHOL, notSkip]

private theorem adjustPc_zero {width : Nat} [NeZero width] (code : LabProgHOL width) :
    adjustPc 0 code = 0 := by rw [adjustPc.eq_def]; simp

private theorem adjustPc_emptySection {width : Nat} [NeZero width]
    (pc k : Nat) (rest : LabProgHOL width) :
    adjustPc pc (⟨k, []⟩ :: rest) = adjustPc pc rest := by
  by_cases h : pc = 0 <;> simp [adjustPc, h, adjustPc_zero]

private theorem adjustPc_label {width : Nat} [NeZero width]
    (pc k : Nat) (line : LabLineHOL width) (lines : List (LabLineHOL width))
    (rest : LabProgHOL width) (h : isLabelHOL line = true) :
    adjustPc pc (⟨k, line :: lines⟩ :: rest) = adjustPc pc (⟨k, lines⟩ :: rest) := by
  by_cases hp : pc = 0 <;> simp [adjustPc, hp, h, adjustPc_zero]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem asmFetchAuxEq {width : Nat} [NeZero width] (pc : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) :
    ∃ count, asmFetchAux (pc + count) code =
      asmFetchAux (adjustPc pc code) (filterSkip code) ∧ allSkips pc code count := by
  induction code generalizing pc with
  | nil =>
    exact ⟨0, by simp [asmFetchAux, filterSkip], by simp [allSkips, asmFetchAux]⟩
  | cons sect rest ih =>
    rcases sect with ⟨k, lines⟩
    induction lines generalizing pc with
    | nil =>
      obtain ⟨count, he, hs⟩ := ih pc
      exact ⟨count, by simpa [asmFetchAux, filterSkip, adjustPc_emptySection] using he,
        by simpa [allSkips, asmFetchAux] using hs⟩
    | cons line lines ih =>
      by_cases hl : isLabelHOL line = true
      · have hn := isLabelNotSkip line hl
        obtain ⟨count, he, hs⟩ := ih pc
        exact ⟨count, by simpa [filterSkip, hn, asmFetchAux, hl, adjustPc_label] using he,
          by simpa [allSkips, asmFetchAux, hl] using hs⟩
      · by_cases hn : notSkip line = true
        · cases pc with
          | zero =>
            refine ⟨0, ?_, ?_⟩
            · simp [adjustPc_zero, filterSkip, hn, asmFetchAux, hl]
            · constructor
              · intro bytes len he
                have heq : line = .asm (.asmi (.inst .skip)) bytes len := by
                  simpa [asmFetchAux, hl] using he
                subst line
                simp [notSkip] at hn
              · simp
          | succ pc =>
            obtain ⟨count, he, hs⟩ := ih pc
            refine ⟨count, ?_, ?_⟩
            · simpa [adjustPc, filterSkip, hn, asmFetchAux, hl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
            · simpa [allSkips, asmFetchAux, hl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
        · have hf : notSkip line = false := Bool.eq_false_iff.mpr hn
          obtain ⟨bytes, len, rfl⟩ := notNotSkipImpSkip line hf
          cases pc with
          | zero =>
            obtain ⟨count, he, hs⟩ := ih 0
            refine ⟨count + 1, ?_, ?_⟩
            · simpa [filterSkip, notSkip, asmFetchAux, isLabelHOL, adjustPc_zero] using he
            · rcases hs with ⟨hstop, hskip⟩
              constructor
              · simpa [asmFetchAux, isLabelHOL] using hstop
              · intro i hi
                cases i with
                | zero => exact ⟨bytes, len, by simp [asmFetchAux, isLabelHOL]⟩
                | succ i =>
                  obtain ⟨b, l, he⟩ := hskip i (by omega)
                  exact ⟨b, l, by simpa [asmFetchAux, isLabelHOL] using he⟩
          | succ pc =>
            obtain ⟨count, he, hs⟩ := ih pc
            refine ⟨count, ?_, ?_⟩
            · simpa [adjustPc, filterSkip, notSkip, asmFetchAux, isLabelHOL, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
            · simpa [allSkips, asmFetchAux, isLabelHOL, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRw {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) (extra : Nat) :
    {s with clock := s.clock} = s ∧ {s with pc := s.pc} = s ∧
      {s with pc := s.pc, clock := s.clock + extra} =
        {s with clock := s.clock + extra} := ⟨rfl, rfl, rfl⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allSkipsEvaluate {width : Nat} [NeZero width] {C F : Type}
    (count : Nat) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    allSkips s.pc s.code count ∧ s.failed = false → ∀ extra,
      evaluate {s with clock := s.clock + extra + count} =
      evaluate {s with pc := s.pc + count, clock := s.clock + extra} := by
  induction count generalizing s with
  | zero => intro _ extra; simp
  | succ count ih =>
    rintro ⟨hs, hfailed⟩ extra
    obtain ⟨bytes, len, hfetch⟩ := hs.2 0 (Nat.succ_pos count)
    simp only [Nat.add_zero] at hfetch
    have hsnext : allSkips (s.pc + 1) s.code count := by
      rcases hs with ⟨hstop, hskip⟩
      constructor
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstop
      · intro i hi
        obtain ⟨b, l, hf⟩ := hskip (i + 1) (by omega)
        exact ⟨b, l, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf⟩
    have hclock : s.clock + extra + (count + 1) ≠ 0 := by omega
    conv => lhs; rw [evaluate]
    simp only [hclock, if_false, asmFetch, hfetch, asmInst, hfailed, Bool.false_eq_true]
    have hpred : s.clock + extra + (count + 1) - 1 = s.clock + extra + count := by omega
    simp only [incPc, decClock, hpred]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hfailed] using
      ih {s with pc := s.pc + 1} ⟨hsnext, hfailed⟩ extra

end Flapjack.Compiler.Backend.LabFilter.Proofs
