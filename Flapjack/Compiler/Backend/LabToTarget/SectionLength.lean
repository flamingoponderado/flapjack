import Flapjack.Compiler.Backend.LabToTarget.Labels
import Flapjack.Compiler.Backend.LabToTarget.Padding
import Flapjack.Compiler.Backend.LabToTarget.LineLength

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Original additive position transport; arbitrary annotations and offsets
are retained without a well-formedness or encoded-byte consistency premise. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_length_add"
  (words_as_type_indexed_bitvec)]
theorem secLengthAdd {width : Nat} [NeZero width]
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (n m : Nat) : secLength lines (n + m) = secLength lines n + m := by
  induction lines generalizing n with
  | nil => rfl
  | cons line lines ih =>
    have addSwap (len : Nat) : n + m + len = (n + len) + m := by omega
    cases line <;> simp only [secLength]
    all_goals
      rw [addSwap]
      exact ih _

/-- The original unconditional position equation retains arbitrary initial
position and accumulated labels; every native line constructor is covered. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "section_labels_sec_length"
  (words_as_type_indexed_bitvec)]
theorem sectionLabelsSecLength {width : Nat} [NeZero width]
    (pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (acc : List (Nat × Nat)) :
    (sectionLabels pos lines acc).1 = secLength lines pos := by
  induction lines generalizing pos acc with
  | nil => rfl
  | cons line lines ih =>
    cases line with
    | label secId labelId len =>
      simp only [sectionLabels, secLength]
      split <;> apply ih
    | asm instruction bytes len => exact ih (pos + len) acc
    | labAsm instruction value bytes len => exact ih (pos + len) acc

/-- Original recorded-length sum equation over every native line. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_length_sum_line_len"
  (words_as_type_indexed_bitvec)]
theorem secLengthSumLineLen {width : Nat} [NeZero width]
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (n : Nat) : secLength lines n = (lines.map lineLen).sum + n := by
  induction lines generalizing n with
  | nil => simp [secLength]
  | cons line lines ih =>
    cases line <;> simp only [secLength, List.map_cons, List.sum_cons, lineLen]
    all_goals
      rw [ih]
      omega

/-- Original whole-pair composition equation. The prior accumulator and
arbitrary recorded line lengths are retained, without a validity premise. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "section_labels_append"
  (words_as_type_indexed_bitvec)]
theorem sectionLabelsAppend {width : Nat} [NeZero width]
    (pos : Nat)
    (left : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (labs : List (Nat × Nat))
    (right : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    sectionLabels pos (left ++ right) labs =
      sectionLabels (pos + (left.map lineLen).sum) right
        (sectionLabels pos left labs).2 := by
  induction left generalizing pos labs with
  | nil => simp [sectionLabels]
  | cons line left ih =>
    cases line with
    | label secId labelId len =>
      simp only [List.cons_append, sectionLabels, List.map_cons, List.sum_cons, lineLen]
      split <;> rw [ih] <;> congr 1 <;> omega
    | asm instruction bytes len =>
      simp only [List.cons_append, sectionLabels, List.map_cons, List.sum_cons, lineLen]
      rw [ih]
      congr 1 <;> omega
    | labAsm instruction value bytes len =>
      simp only [List.cons_append, sectionLabels, List.map_cons, List.sum_cons, lineLen]
      rw [ih]
      congr 1 <;> omega

end Flapjack.Compiler.Backend.LabToTarget
