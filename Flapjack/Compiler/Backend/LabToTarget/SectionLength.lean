import Flapjack.Compiler.Backend.LabToTarget.Labels
import Flapjack.Compiler.Backend.LabToTarget.Padding

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

end Flapjack.Compiler.Backend.LabToTarget
