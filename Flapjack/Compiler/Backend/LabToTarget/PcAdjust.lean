module

public import Flapjack.Compiler.Backend.LabToTarget.Fetch
public import Flapjack.Compiler.Backend.LabToTarget.FilterSkip
public import Flapjack.Compiler.Backend.LabFilter.Proofs.PcAdjustment
public import Mathlib.Data.Nat.Find

@[expose] public section

-- Private helpers below are Flapjack infrastructure with no separate HOL original.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! `all_pc_adjust_pc`: every filtered program index is `adjust_pc` of some
source PC.  The proof walks `adjust_pc` as a step function of its source PC:
it starts at 0, rises by at most one per source line, and reaches
`num_pcs (filter_skip code)` after the non-label lines, so it passes through
every value below that count. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack.Basis.Pure.MlString

/-- Flapjack infrastructure: number of non-label lines in a section. -/
private def nonLabelLines {width : Nat} [NeZero width] (xs : List (LabLineHOL width)) : Nat :=
  (xs.filter (fun l => isLabelHOL l = false)).length

/-- Flapjack infrastructure: number of instructions `filter_skip` keeps from a
section, i.e. its non-skip, non-label lines. -/
private def keptLines {width : Nat} [NeZero width] (xs : List (LabLineHOL width)) : Nat :=
  ((xs.filter notSkip).filter (fun l => isLabelHOL l = false)).length

/-- Flapjack infrastructure: `numPcs` of a non-empty-section head equals the
non-label line count of that section plus `numPcs` of the rest. -/
private theorem numPcs_section {width : Nat} [NeZero width] (k : Nat)
    (xs : List (LabLineHOL width)) (rest : LabProgHOL width) :
    numPcs (⟨k, xs⟩ :: rest) = nonLabelLines xs + numPcs rest := by
  induction xs with
  | nil => simp [numPcs, nonLabelLines]
  | cons l ls ih =>
    by_cases hl : isLabelHOL l = true
    · simp [numPcs, nonLabelLines, hl, ih]
    · have hf : isLabelHOL l = false := Bool.eq_false_iff.mpr hl
      simp [numPcs, nonLabelLines, hf, ih]
      omega

/-- Flapjack infrastructure: `numPcs (filter_skip code)` counts exactly the
kept (non-skip, non-label) lines of the whole program. -/
private theorem numPcs_filterSkip {width : Nat} [NeZero width] (code : LabProgHOL width) :
    numPcs (filterSkip code) = (code.map (fun sec => keptLines sec.lines)).sum := by
  induction code with
  | nil => simp [filterSkip, numPcs]
  | cons sec rest ih =>
    rcases sec with ⟨k, xs⟩
    simp only [filterSkip, List.map_cons, List.sum_cons]
    rw [numPcs_section, ih]
    simp only [keptLines, nonLabelLines]

/-- Flapjack infrastructure: `adjustPc 0 code = 0`, the literal first clause. -/
private theorem adjustPc_zeroHOL {width : Nat} [NeZero width] (code : LabProgHOL width) :
    adjustPc 0 code = 0 := by
  rw [adjustPc.eq_def]
  rw [if_pos rfl]

/-- Flapjack infrastructure: an empty section does not change `adjustPc`. -/
private theorem adjustPc_emptyHOL {width : Nat} [NeZero width] (pc k : Nat)
    (rest : LabProgHOL width) :
    adjustPc pc (⟨k, []⟩ :: rest) = adjustPc pc rest := by
  by_cases hp : pc = 0
  · subst hp
    rw [adjustPc_zeroHOL, adjustPc_zeroHOL]
  · rw [adjustPc.eq_def]
    rw [if_neg hp]

/-- Flapjack infrastructure: one non-empty section step of `adjustPc` for a
nonzero source PC, as the literal definition writes it. -/
private theorem adjustPc_consHOL {width : Nat} [NeZero width] (pc k : Nat)
    (l : LabLineHOL width) (ls : List (LabLineHOL width)) (rest : LabProgHOL width)
    (hpc : pc ≠ 0) :
    adjustPc pc (⟨k, l :: ls⟩ :: rest) =
      if isLabelHOL l then adjustPc pc (⟨k, ls⟩ :: rest)
      else if notSkip l then adjustPc (pc - 1) (⟨k, ls⟩ :: rest) + 1
      else adjustPc (pc - 1) (⟨k, ls⟩ :: rest) := by
  rw [adjustPc.eq_def]
  rw [if_neg hpc]

/-- Flapjack infrastructure: walking one section advances `adjustPc` by its kept
line count and lowers the source PC by its non-label line count, provided the
source PC covers that many non-label lines. -/
private theorem adjustPc_section {width : Nat} [NeZero width] (k : Nat)
    (xs : List (LabLineHOL width)) (rest : LabProgHOL width) (pc : Nat)
    (hpc : nonLabelLines xs ≤ pc) :
    adjustPc pc (⟨k, xs⟩ :: rest) = adjustPc (pc - nonLabelLines xs) rest + keptLines xs := by
  induction xs generalizing pc with
  | nil =>
    simpa only [nonLabelLines, keptLines, List.filter_nil, List.length_nil,
      Nat.sub_zero, Nat.add_zero] using adjustPc_emptyHOL pc k rest
  | cons l ls ih =>
    by_cases hl : isLabelHOL l = true
    · have hNL : nonLabelLines (l :: ls) = nonLabelLines ls := by
        simp [nonLabelLines, hl]
      have hKL : keptLines (l :: ls) = keptLines ls := by
        simp [keptLines, hl]
      have hpc' : nonLabelLines ls ≤ pc := by
        rw [hNL] at hpc
        exact hpc
      have hstep : adjustPc pc (⟨k, l :: ls⟩ :: rest) =
          adjustPc pc (⟨k, ls⟩ :: rest) := by
        by_cases hp : pc = 0
        · subst hp
          rw [adjustPc_zeroHOL, adjustPc_zeroHOL]
        · rw [adjustPc_consHOL pc k l ls rest hp]
          rw [if_pos hl]
      rw [hstep, hNL, hKL]
      exact ih pc hpc'
    · have hf : isLabelHOL l = false := Bool.eq_false_iff.mpr hl
      have hNL : nonLabelLines (l :: ls) = 1 + nonLabelLines ls := by
        simp [nonLabelLines, hf]
        omega
      have hpc' : nonLabelLines ls ≤ pc - 1 := by
        rw [hNL] at hpc
        omega
      have hpc0 : pc ≠ 0 := by omega
      by_cases hn : notSkip l = true
      · have hKL : keptLines (l :: ls) = 1 + keptLines ls := by
          simp [keptLines, hf, hn]
          omega
        have hstep : adjustPc pc (⟨k, l :: ls⟩ :: rest) =
            adjustPc (pc - 1) (⟨k, ls⟩ :: rest) + 1 := by
          rw [adjustPc_consHOL pc k l ls rest hpc0]
          rw [if_neg hl]
          rw [if_pos hn]
        rw [hstep, hNL, hKL, ih (pc - 1) hpc']
        have harg : pc - 1 - nonLabelLines ls = pc - (1 + nonLabelLines ls) := by
          omega
        rw [harg]
        omega
      · have hf2 : notSkip l = false := Bool.eq_false_iff.mpr hn
        have hn' : ¬ notSkip l = true := by
          rw [hf2]
          simp
        have hKL : keptLines (l :: ls) = keptLines ls := by
          simp [keptLines, hf2]
        have hstep : adjustPc pc (⟨k, l :: ls⟩ :: rest) =
            adjustPc (pc - 1) (⟨k, ls⟩ :: rest) := by
          rw [adjustPc_consHOL pc k l ls rest hpc0]
          rw [if_neg hl]
          rw [if_neg hn']
        rw [hstep, hNL, hKL, ih (pc - 1) hpc']
        have harg : pc - 1 - nonLabelLines ls = pc - (1 + nonLabelLines ls) := by
          omega
        rw [harg]

/-- Flapjack infrastructure: `adjustPc` reaches `numPcs (filter_skip code)` after
the non-label lines, so it attains every filtered index below that count. -/
private theorem adjustPc_nonLabel {width : Nat} [NeZero width] (code : LabProgHOL width) :
    adjustPc ((code.map (fun sec => nonLabelLines sec.lines)).sum) code =
      numPcs (filterSkip code) := by
  induction code with
  | nil => simp [adjustPc, filterSkip, numPcs]
  | cons sec rest ih =>
    rcases sec with ⟨k, xs⟩
    simp only [List.map_cons, List.sum_cons]
    rw [adjustPc_section k xs rest
      (nonLabelLines xs + (List.map (fun sec => nonLabelLines sec.lines) rest).sum)
      (by omega)]
    have hsub : nonLabelLines xs +
        (List.map (fun sec => nonLabelLines sec.lines) rest).sum - nonLabelLines xs =
        (List.map (fun sec => nonLabelLines sec.lines) rest).sum := by omega
    rw [hsub, ih]
    rw [numPcs_filterSkip]
    rw [numPcs_filterSkip]
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Flapjack infrastructure: advancing the source PC by one changes `adjustPc` by
zero or one, the step law used by `all_pc_adjust_pc`. -/
private theorem adjustPc_step {width : Nat} [NeZero width] (pc : Nat) (code : LabProgHOL width) :
    adjustPc (pc + 1) code = adjustPc pc code ∨
      adjustPc (pc + 1) code = adjustPc pc code + 1 := by
  by_cases h : ∃ bytes len, asmFetchAux pc code =
      some (.asm (.asmi (.inst .skip)) bytes len)
  · obtain ⟨bytes, len, hf⟩ := h
    exact Or.inl ((adjustPcSucc pc code).1 bytes len hf)
  · refine Or.inr ((adjustPcSucc pc code).2 ?_)
    intro bytes len hf
    exact h ⟨bytes, len, hf⟩

/-- Exact HOL `all_pc_adjust_pc` (`lab_to_targetProofScript.sml:10729-10789`):
every index below `numPcs (filterSkip code)` is the adjusted PC of some source
PC. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_pc_adjust_pc"
  (words_as_type_indexed_bitvec)]
theorem allPcAdjustPc {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (p : Nat)
    (hp : p < numPcs (filterSkip code)) :
    ∃ k, adjustPc k code = p := by
  classical
  have hzero : adjustPc 0 code = 0 := adjustPc_zeroHOL code
  by_cases hp0 : p = 0
  · subst hp0
    exact ⟨0, hzero⟩
  · have hexists : ∃ k, p ≤ adjustPc k code := by
      refine ⟨(code.map (fun sec => nonLabelLines sec.lines)).sum, ?_⟩
      rw [adjustPc_nonLabel]
      omega
    have hk_spec : p ≤ adjustPc (Nat.find hexists) code := Nat.find_spec hexists
    have hk_pos : 0 < Nat.find hexists := by
      rcases Nat.eq_zero_or_pos (Nat.find hexists) with h0 | hpos
      · rw [h0, hzero] at hk_spec
        omega
      · exact hpos
    have hk_prev : ¬ p ≤ adjustPc (Nat.find hexists - 1) code :=
      Nat.find_min hexists (by omega)
    have hstep := adjustPc_step (Nat.find hexists - 1) code
    have he : Nat.find hexists - 1 + 1 = Nat.find hexists := by omega
    refine ⟨Nat.find hexists, ?_⟩
    rcases hstep with h | h
    · rw [he] at h
      omega
    · rw [he] at h
      omega

end Flapjack.Compiler.Backend.LabToTarget
