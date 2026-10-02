import Flapjack.Compiler.Backend.LabToTarget.LabelPosition
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.LabelUpdates
import Flapjack.Compiler.Backend.LabToTarget.UpdatePosition
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original unconditional establishment by the actual label updater.
Input annotations, bytes, stored words and starting position are unrestricted. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_upd_lab_len_pos_ok"
  (words_as_type_indexed_bitvec)]
theorem linesUpdLabLen_posOk {width : Nat} [NeZero width] (pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    labLenPosOk pos (linesUpdLabLen pos lines []).1 := by
  induction lines generalizing pos with
  | nil => simp [linesUpdLabLen,labLenPosOk]
  | cons line tail ih =>
    cases line with
    | label k1 k2 len =>
      simp only [linesUpdLabLen]
      rw [linesUpdLabLen_aux]
      by_cases he : pos % 2 = 0
      · simpa [labLenPosOk,lineLabLenPosOk,lineLen,he] using ih pos
      · simpa [labLenPosOk,lineLabLenPosOk,lineLen,he] using ih (pos+1)
    | asm a bytes len =>
      simp only [linesUpdLabLen]
      rw [linesUpdLabLen_aux]
      simpa [labLenPosOk,lineLabLenPosOk,lineLen] using ih (pos+len)
    | labAsm a w bytes len =>
      simp only [linesUpdLabLen]
      rw [linesUpdLabLen_aux]
      simpa [labLenPosOk,lineLabLenPosOk,lineLen] using ih (pos+len)

/-- Full original section-list establishment. The updater's actual returned
position is identified with secLength by the original SND conservation law. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "upd_lab_len_pos_ok"
  (words_as_type_indexed_bitvec)]
theorem updLabLen_posOk {width : Nat} [NeZero width] (pos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allLabLenPosOk pos (updLabLen pos code) := by
  induction code generalizing pos with
  | nil => simp [updLabLen,allLabLenPosOk]
  | cons sec rest ih =>
    rcases sec with ⟨id,lines⟩
    have hline := linesUpdLabLen_posOk pos lines
    have hposition := linesUpdLabLen_position pos lines []
    have ht := ih (linesUpdLabLen pos lines []).2
    simp only [updLabLen,allLabLenPosOk]
    refine ⟨hline,?_⟩
    simpa [secLengthSumLineLen,hposition,Nat.add_comm] using ht
end Flapjack.Compiler.Backend.LabToTarget
