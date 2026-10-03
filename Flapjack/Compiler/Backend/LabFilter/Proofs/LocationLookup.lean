import Flapjack.Compiler.Backend.LabFilter.Proofs.PcAdjustment

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- Literal zero-PC equation; Flapjack infrastructure with no separate HOL declaration. -/
private theorem adjustPcZero {width : Nat} [NeZero width] (code : LabProgHOL width) :
    adjustPc 0 code = 0 := by rw [adjustPc.eq_def]; simp

/-- Literal section-entry lookup equation; Flapjack infrastructure with no separate HOL declaration. -/
private theorem locToPcMatchedSection {width : Nat} [NeZero width]
    (n1 n2 k : Nat) (lines : List (LabLineHOL width)) (rest : LabProgHOL width)
    (h : k = n1 ∧ n2 = 0) : locToPc n1 n2 (⟨k, lines⟩ :: rest) = some 0 := by
  rw [locToPc.eq_def]
  simp [h]

/-- Literal label-line adjustment equation; Flapjack infrastructure with no separate HOL declaration. -/
private theorem adjustPcLabel {width : Nat} [NeZero width]
    (pc k : Nat) (line : LabLineHOL width) (lines : List (LabLineHOL width))
    (rest : LabProgHOL width) (h : isLabelHOL line = true) :
    adjustPc pc (⟨k, line :: lines⟩ :: rest) = adjustPc pc (⟨k, lines⟩ :: rest) := by
  by_cases hp : pc = 0 <;> simp [adjustPc, hp, h, adjustPcZero]

/-- Literal nonlabel lookup equation; Flapjack infrastructure with no separate HOL declaration. -/
private theorem locToPcNonLabel {width : Nat} [NeZero width]
    (n1 n2 k : Nat) (line : LabLineHOL width) (lines : List (LabLineHOL width))
    (rest : LabProgHOL width) (h : ¬(k = n1 ∧ n2 = 0)) (hl : isLabelHOL line ≠ true) :
    locToPc n1 n2 (⟨k, line :: lines⟩ :: rest) =
      (locToPc n1 n2 (⟨k, lines⟩ :: rest)).map (fun pc => pc + 1) := by
  cases line <;> simp_all [locToPc, isLabelHOL]

/-- Flapjack lookup/PC transformation equation assembling the original NONE/SOME
clauses; no separately named HOL original. -/
private theorem locToPcFilterMap {width : Nat} [NeZero width] (n1 n2 : Nat)
    (code : LabProgHOL width) :
    locToPc n1 n2 (filterSkip code) =
      (locToPc n1 n2 code).map (fun pc => adjustPc pc code) := by
  induction code with
  | nil => simp [locToPc, filterSkip]
  | cons sect rest ih =>
    rcases sect with ⟨k, lines⟩
    induction lines with
    | nil =>
      by_cases h : k = n1 ∧ n2 = 0
      · simp [locToPc, filterSkip, h, adjustPcZero]
      · simp only [filterSkip, List.filter_nil, locToPc, h, ↓reduceIte]
        rw [ih]
        cases he : locToPc n1 n2 rest with
        | none => rfl
        | some pc => cases pc <;> simp [adjustPc, adjustPcZero]
    | cons line lines ih =>
      by_cases h : k = n1 ∧ n2 = 0
      · rw [locToPcMatchedSection n1 n2 k _ _ h]
        simp only [filterSkip]
        rw [locToPcMatchedSection n1 n2 k _ _ h]
        simp [adjustPcZero]
      · by_cases hl : isLabelHOL line = true
        · cases line with
          | label ownSection ownLabel len =>
            simp only [filterSkip, List.filter_cons, notSkip, ↓reduceIte]
            by_cases hm : (ownSection = n1 ∧ ownLabel = n2) ∧ n2 ≠ 0
            · simp [locToPc, hm, adjustPcZero]
            · simp only [locToPc, h, hm, Bool.and_eq_true, beq_iff_eq,
                bne_iff_ne, ↓reduceIte, isLabelHOL]
              have heq : (fun pc => adjustPc pc (⟨k, .label ownSection ownLabel len :: lines⟩ :: rest)) =
                  (fun pc => adjustPc pc (⟨k, lines⟩ :: rest)) := by
                funext pc
                exact adjustPcLabel pc k _ lines rest hl
              rw [heq]
              exact ih
          | asm => simp [isLabelHOL] at hl
          | labAsm => simp [isLabelHOL] at hl
        · by_cases hn : notSkip line = true
          · simp only [filterSkip, List.filter_cons, hn, ↓reduceIte]
            rw [locToPcNonLabel n1 n2 k line _ _ h hl]
            rw [locToPcNonLabel n1 n2 k line _ _ h hl]
            simp only [filterSkip] at ih
            rw [ih]
            cases he : locToPc n1 n2 (⟨k, lines⟩ :: rest) <;>
              simp [adjustPc, hl, hn]
          · simp only [filterSkip, List.filter_cons, hn, Bool.false_eq_true, ↓reduceIte]
            rw [locToPcNonLabel n1 n2 k line _ _ h hl]
            simp only [filterSkip] at ih
            rw [ih]
            cases he : locToPc n1 n2 (⟨k, lines⟩ :: rest) <;>
              simp [adjustPc, hl, hn]

@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "loc_to_pc_eq_NONE"
  (words_as_type_indexed_bitvec)]
theorem locToPcEqNone {width : Nat} [NeZero width] (n1 n2 : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) :
    locToPc n1 n2 (filterSkip code) = none → locToPc n1 n2 code = none := by
  intro h
  rw [locToPcFilterMap] at h
  cases he : locToPc n1 n2 code <;> simp_all

@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "loc_to_pc_eq_SOME"
  (words_as_type_indexed_bitvec)]
theorem locToPcEqSome {width : Nat} [NeZero width] (n1 n2 : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) (pc : Nat) :
    locToPc n1 n2 (filterSkip code) = some pc →
    ∃ originalPc, locToPc n1 n2 code = some originalPc ∧ adjustPc originalPc code = pc := by
  intro h
  rw [locToPcFilterMap] at h
  cases he : locToPc n1 n2 code with
  | none => simp [he] at h
  | some originalPc => exact ⟨originalPc, rfl, by simpa only [he, Option.map_some, Option.some.injEq] using h⟩

@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "loc_to_pc_adjust_pc_append"
  (words_as_type_indexed_bitvec)]
theorem locToPcAdjustPcAppend {width : Nat} [NeZero width] (n1 n2 : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) (pc : Nat) (rest : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) :
    locToPc n1 n2 code = some pc → adjustPc pc code = adjustPc pc (code ++ rest) := by
  fun_induction locToPc n1 n2 code generalizing pc
  all_goals intro hs
  all_goals simp_all [adjustPc]
  case case2 => subst pc; simp [adjustPcZero]
  case case6 =>
    obtain ⟨originalPc, hlookup, rfl⟩ := hs
    simp_all

end Flapjack.Compiler.Backend.LabFilter.Proofs
