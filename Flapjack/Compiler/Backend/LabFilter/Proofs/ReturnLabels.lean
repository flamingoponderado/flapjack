import Flapjack.Compiler.Backend.LabFilter.Proofs.LocationLookup

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "next_label_filter_skip"
  (words_as_type_indexed_bitvec)]
theorem nextLabelFilterSkip {width : Nat} {resultWidth : Nat} [NeZero width] [NeZero resultWidth]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) :
    nextLabel (resultWidth := resultWidth) code = nextLabel (resultWidth := resultWidth) (filterSkip code) := by
  induction code with
  | nil => simp [nextLabel, filterSkip]
  | cons sect rest ih =>
    rcases sect with ⟨k, lines⟩
    induction lines with
    | nil => simpa [nextLabel, filterSkip] using ih
    | cons line lines ih =>
      by_cases hn : notSkip line = true
      · cases line <;> simp_all [nextLabel, filterSkip]
      · cases line <;> simp_all [nextLabel, filterSkip, notSkip]

@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "all_skips_get_lab_after"
  (words_as_type_indexed_bitvec)]
theorem allSkipsGetLabAfter {width : Nat} {resultWidth : Nat} [NeZero width] [NeZero resultWidth]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) (count : Nat) :
    allSkips 0 code count → getLabAfter (resultWidth := resultWidth) count code = getLabAfter (resultWidth := resultWidth) 0 (filterSkip code) := by
  induction code generalizing count with
  | nil => simp [getLabAfter, filterSkip]
  | cons sect rest ih =>
    rcases sect with ⟨k, lines⟩
    induction lines generalizing count with
    | nil => simpa [getLabAfter, filterSkip, allSkips, asmFetchAux] using ih count
    | cons line lines ih =>
      intro hs
      by_cases hl : isLabelHOL line = true
      · have hn := isLabelNotSkip line hl
        have ht : allSkips 0 (⟨k, lines⟩ :: rest) count := by
          simpa [allSkips, asmFetchAux, hl] using hs
        simpa [getLabAfter, filterSkip, hn, hl] using ih count ht
      · cases count with
        | zero =>
          have hn : notSkip line = true := by
            by_contra hn
            obtain ⟨bytes, len, rfl⟩ := notNotSkipImpSkip line (Bool.eq_false_iff.mpr hn)
            have h := hs.1 bytes len
            simp [asmFetchAux, isLabelHOL] at h
          simpa [getLabAfter, filterSkip, hn, hl] using
            nextLabelFilterSkip (resultWidth := resultWidth) (⟨k, lines⟩ :: rest)
        | succ count =>
          obtain ⟨bytes, len, hf⟩ := hs.2 0 (Nat.succ_pos count)
          have he : line = .asm (.asmi (.inst .skip)) bytes len := by
            simpa [asmFetchAux, hl] using hf
          subst line
          have ht : allSkips 0 (⟨k, lines⟩ :: rest) count := by
            constructor
            · simpa [asmFetchAux, isLabelHOL] using hs.1
            · intro i hi
              obtain ⟨b, l, he⟩ := hs.2 (i + 1) (by omega)
              exact ⟨b, l, by simpa [asmFetchAux, isLabelHOL] using he⟩
          simpa [getLabAfter, filterSkip, notSkip, isLabelHOL] using ih count ht

/-- Literal zero-PC equation; Flapjack infrastructure with no separate HOL declaration. -/
private theorem adjustPcZero {width : Nat} [NeZero width] (code : LabProgHOL width) :
    adjustPc 0 code = 0 := by rw [adjustPc.eq_def]; simp

@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "get_lab_after_adjust"
  (words_as_type_indexed_bitvec)]
theorem getLabAfterAdjust {width : Nat} {resultWidth : Nat} [NeZero width] [NeZero resultWidth] (pc : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) (count : Nat) :
    allSkips pc code count →
    getLabAfter (resultWidth := resultWidth) (pc + count) code = getLabAfter (resultWidth := resultWidth) (adjustPc pc code) (filterSkip code) := by
  induction code generalizing pc count with
  | nil => simp [getLabAfter, filterSkip]
  | cons sect rest ih =>
    rcases sect with ⟨k, lines⟩
    induction lines generalizing pc count with
    | nil =>
      intro hs
      have ht : allSkips pc rest count := by simpa [allSkips, asmFetchAux] using hs
      cases pc with
      | zero => simpa [getLabAfter, filterSkip, adjustPcZero] using ih 0 count ht
      | succ pc => simpa [getLabAfter, filterSkip, adjustPc] using ih (pc + 1) count ht
    | cons line lines ih =>
      intro hs
      cases pc with
      | zero => simpa [adjustPcZero] using allSkipsGetLabAfter (resultWidth := resultWidth) _ count hs
      | succ pc =>
        by_cases hl : isLabelHOL line = true
        · have hn := isLabelNotSkip line hl
          have ht : allSkips (pc + 1) (⟨k, lines⟩ :: rest) count := by
            simpa [allSkips, asmFetchAux, hl] using hs
          simpa [getLabAfter, filterSkip, adjustPc, hl, hn] using ih (pc + 1) count ht
        · have ht : allSkips pc (⟨k, lines⟩ :: rest) count := by
            simpa [allSkips, asmFetchAux, hl, Nat.add_right_comm] using hs
          by_cases hn : notSkip line = true
          · simpa [getLabAfter, filterSkip, adjustPc, hl, hn, Nat.add_right_comm] using ih pc count ht
          · simpa [getLabAfter, filterSkip, adjustPc, hl, hn, Nat.add_right_comm] using ih pc count ht

end Flapjack.Compiler.Backend.LabFilter.Proofs
